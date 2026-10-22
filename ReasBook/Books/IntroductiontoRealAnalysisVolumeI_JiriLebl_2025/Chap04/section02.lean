/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open Set Filter
open scoped Topology

section Chap04
section Section02

/-- Definition 4.2.1: A function `f : S → ℝ` has a relative maximum at `c ∈ S`
if some `δ > 0` satisfies `f x ≤ f c` whenever `x ∈ S` and `|x - c| < δ`.
The notion of relative minimum reverses the inequality. -/
def RelativeMaxOn (S : Set ℝ) (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ δ > 0, ∀ {x}, x ∈ S → |x - c| < δ → f x ≤ f c

def RelativeMinOn (S : Set ℝ) (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ δ > 0, ∀ {x}, x ∈ S → |x - c| < δ → f c ≤ f x

/-- The relative maximum defined via punctured-`δ` neighborhoods matches
`IsLocalMaxOn` from mathlib. -/
lemma relativeMaxOn_iff_isLocalMaxOn {S : Set ℝ} {f : ℝ → ℝ} {c : ℝ} :
    RelativeMaxOn S f c ↔ IsLocalMaxOn f S c := by
  constructor
  · rintro ⟨δ, hδpos, hδ⟩
    have hsubset : Metric.ball c δ ∩ S ⊆ {x | f x ≤ f c} := by
      intro x hx
      have hxlt : |x - c| < δ := by
        have hdist : dist x c < δ := hx.1
        simpa [Real.dist_eq] using hdist
      exact hδ hx.2 hxlt
    have hmem : {x | f x ≤ f c} ∈ 𝓝[S] c :=
      (Metric.mem_nhdsWithin_iff).2 ⟨δ, hδpos, hsubset⟩
    simpa [IsLocalMaxOn, IsMaxFilter] using hmem
  · intro hloc
    have hmem : {x | f x ≤ f c} ∈ 𝓝[S] c := by
      simpa [IsLocalMaxOn, IsMaxFilter] using hloc
    rcases (Metric.mem_nhdsWithin_iff).1 hmem with ⟨δ, hδpos, hsubset⟩
    refine ⟨δ, hδpos, ?_⟩
    intro x hx hxlt
    have hxball : x ∈ Metric.ball c δ := by
      have hdist : dist x c < δ := by simpa [Real.dist_eq] using hxlt
      simpa using hdist
    exact hsubset ⟨hxball, hx⟩

/-- The relative minimum defined via punctured-`δ` neighborhoods matches
`IsLocalMinOn` from mathlib. -/
lemma relativeMinOn_iff_isLocalMinOn {S : Set ℝ} {f : ℝ → ℝ} {c : ℝ} :
    RelativeMinOn S f c ↔ IsLocalMinOn f S c := by
  constructor
  · rintro ⟨δ, hδpos, hδ⟩
    have hsubset : Metric.ball c δ ∩ S ⊆ {x | f c ≤ f x} := by
      intro x hx
      have hxlt : |x - c| < δ := by
        have hdist : dist x c < δ := hx.1
        simpa [Real.dist_eq] using hdist
      exact hδ hx.2 hxlt
    have hmem : {x | f c ≤ f x} ∈ 𝓝[S] c :=
      (Metric.mem_nhdsWithin_iff).2 ⟨δ, hδpos, hsubset⟩
    simpa [IsLocalMinOn, IsMinFilter] using hmem
  · intro hloc
    have hmem : {x | f c ≤ f x} ∈ 𝓝[S] c := by
      simpa [IsLocalMinOn, IsMinFilter] using hloc
    rcases (Metric.mem_nhdsWithin_iff).1 hmem with ⟨δ, hδpos, hsubset⟩
    refine ⟨δ, hδpos, ?_⟩
    intro x hx hxlt
    have hxball : x ∈ Metric.ball c δ := by
      have hdist : dist x c < δ := by simpa [Real.dist_eq] using hxlt
      simpa using hdist
    exact hsubset ⟨hxball, hx⟩

/-- Lemma 4.2.2: If `f : (a, b) → ℝ` is differentiable at `c ∈ (a, b)`
and has a relative minimum or maximum at `c`, then `deriv f c = 0`. -/
lemma deriv_eq_zero_of_relative_extremum
    {f : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Set.Ioo a b)
    (hf : DifferentiableAt ℝ f c)
    (hExt : RelativeMaxOn (Set.Ioo a b) f c ∨ RelativeMinOn (Set.Ioo a b) f c) :
    deriv f c = 0 := by
  have hloc :
      IsLocalMaxOn f (Set.Ioo a b) c ∨ IsLocalMinOn f (Set.Ioo a b) c := by
    cases hExt with
    | inl hmax =>
        left
        exact (relativeMaxOn_iff_isLocalMaxOn).1 hmax
    | inr hmin =>
        right
        exact (relativeMinOn_iff_isLocalMinOn).1 hmin
  have hopen : Set.Ioo a b ∈ 𝓝 c := isOpen_Ioo.mem_nhds hc
  cases hloc with
  | inl hmax =>
      have hLocal : IsLocalMax f c := hmax.isLocalMax hopen
      simpa using hLocal.hasDerivAt_eq_zero hf.hasDerivAt
  | inr hmin =>
      have hLocal : IsLocalMin f c := hmin.isLocalMin hopen
      simpa using hLocal.hasDerivAt_eq_zero hf.hasDerivAt

/-- Theorem 4.2.3 (Rolle): If `f : [a, b] → ℝ` is continuous on the closed
interval, differentiable on the open interval, and satisfies `f a = f b`,
then there exists some `c ∈ (a, b)` with `deriv f c = 0`. -/
theorem rolle
    {f : ℝ → ℝ} {a b : ℝ} (h₁ : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hend : f a = f b) :
    ∃ c ∈ Set.Ioo a b, deriv f c = 0 := by
  classical
  have hle : a ≤ b := h₁.le
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hnonempty : (Set.Icc a b).Nonempty := ⟨a, ⟨le_rfl, hle⟩⟩
  obtain ⟨cmin, hcmin, hmin⟩ :=
    hcompact.exists_isMinOn hnonempty hcont
  obtain ⟨cmax, hcmax, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty hcont
  have hmin_on : ∀ x ∈ Set.Icc a b, f cmin ≤ f x := by
    simpa [isMinOn_iff] using hmin
  have hmax_on : ∀ x ∈ Set.Icc a b, f x ≤ f cmax := by
    simpa [isMaxOn_iff] using hmax
  have hmax_ge : f a ≤ f cmax := hmax_on _ ⟨le_rfl, hle⟩
  have hmin_le : f cmin ≤ f a := hmin_on _ ⟨le_rfl, hle⟩
  by_cases hmax_gt : f cmax > f a
  · have hne_a : cmax ≠ a := by
      intro h
      have : f cmax = f a := by simp [h]
      linarith
    have hne_b : cmax ≠ b := by
      intro h
      have : f cmax = f b := by simp [h]
      have : f cmax = f a := by simpa [hend] using this
      linarith
    have hlt_a : a < cmax := lt_of_le_of_ne hcmax.1 hne_a.symm
    have hlt_b : cmax < b := lt_of_le_of_ne hcmax.2 hne_b
    have hcmaxIoo : cmax ∈ Set.Ioo a b := ⟨hlt_a, hlt_b⟩
    have hrelmax : RelativeMaxOn (Set.Ioo a b) f cmax := by
      refine ⟨1, by norm_num, ?_⟩
      intro x hx _hxlt
      have hxIcc : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
      exact hmax_on x hxIcc
    have hdiff_cmax : DifferentiableAt ℝ f cmax :=
      hdiff.differentiableAt (isOpen_Ioo.mem_nhds hcmaxIoo)
    exact
      ⟨cmax, hcmaxIoo,
        deriv_eq_zero_of_relative_extremum hcmaxIoo hdiff_cmax (Or.inl hrelmax)⟩
  · have hmax_eq : f cmax = f a := le_antisymm (le_of_not_gt hmax_gt) hmax_ge
    by_cases hmin_lt : f cmin < f a
    · have hne_a : cmin ≠ a := by
        intro h
        have : f cmin = f a := by simp [h]
        linarith
      have hne_b : cmin ≠ b := by
        intro h
        have : f cmin = f b := by simp [h]
        have : f cmin = f a := by simpa [hend] using this
        linarith
      have hlt_a : a < cmin := lt_of_le_of_ne hcmin.1 hne_a.symm
      have hlt_b : cmin < b := lt_of_le_of_ne hcmin.2 hne_b
      have hcminIoo : cmin ∈ Set.Ioo a b := ⟨hlt_a, hlt_b⟩
      have hrelmin : RelativeMinOn (Set.Ioo a b) f cmin := by
        refine ⟨1, by norm_num, ?_⟩
        intro x hx _hxlt
        have hxIcc : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
        exact hmin_on x hxIcc
      have hdiff_cmin : DifferentiableAt ℝ f cmin :=
        hdiff.differentiableAt (isOpen_Ioo.mem_nhds hcminIoo)
      exact
        ⟨cmin, hcminIoo,
          deriv_eq_zero_of_relative_extremum hcminIoo hdiff_cmin (Or.inr hrelmin)⟩
    · have hmin_eq : f cmin = f a :=
        le_antisymm hmin_le (le_of_not_gt hmin_lt)
      have hconst : ∀ x ∈ Set.Icc a b, f x = f a := by
        intro x hx
        have hx_ge : f a ≤ f x := by
          have hx_ge' : f cmin ≤ f x := hmin_on x hx
          simpa [hmin_eq] using hx_ge'
        have hx_le : f x ≤ f a := by
          have hx_le' : f x ≤ f cmax := hmax_on x hx
          simpa [hmax_eq] using hx_le'
        exact le_antisymm hx_le hx_ge
      have hconstIoo : ∀ x ∈ Set.Ioo a b, f x = f a := fun x hx =>
        hconst x ⟨hx.1.le, hx.2.le⟩
      have hcIoo_mid : (a + b) / 2 ∈ Set.Ioo a b := by
        constructor <;> linarith
      let c : ℝ := (a + b) / 2
      have hcIoo : c ∈ Set.Ioo a b := by
        simpa [c] using hcIoo_mid
      have hdiff_c : DifferentiableAt ℝ f c :=
        hdiff.differentiableAt (isOpen_Ioo.mem_nhds hcIoo)
      have hrelmax : RelativeMaxOn (Set.Ioo a b) f c := by
        refine ⟨1, by norm_num, ?_⟩
        intro x hx _hxlt
        have hxconst : f x = f a := hconstIoo x hx
        have hcconst : f c = f a := hconstIoo c hcIoo
        simp [hxconst, hcconst]
      exact
        ⟨c, hcIoo, deriv_eq_zero_of_relative_extremum hcIoo hdiff_c (Or.inl hrelmax)⟩

/-- Theorem 4.2.4 (Mean value theorem): If `f : [a, b] → ℝ` is continuous on
the closed interval and differentiable on the open interval, then some
`c ∈ (a, b)` satisfies `f b - f a = deriv f c * (b - a)`. -/
theorem mean_value_theorem
    {f : ℝ → ℝ} {a b : ℝ} (h₁ : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ c ∈ Set.Ioo a b, f b - f a = deriv f c * (b - a) := by
  classical
  have hne : b - a ≠ 0 := sub_ne_zero.mpr h₁.ne'
  let m : ℝ := (f b - f a) / (b - a)
  let g : ℝ → ℝ := fun x => f x - f b - m * (x - b)
  have hmul : m * (b - a) = f b - f a := by
    change ((f b - f a) / (b - a)) * (b - a) = f b - f a
    field_simp [hne]
  have hga : g a = 0 := by
    calc
      g a = f a - f b - m * (a - b) := rfl
      _ = f a - f b + m * (b - a) := by ring
      _ = f a - f b + (f b - f a) := by simp [hmul]
      _ = 0 := by ring
  have hgb : g b = 0 := by
    simp [g]
  have hcont_const : ContinuousOn (fun _ => f b) (Set.Icc a b) :=
    continuous_const.continuousOn
  have hcont_linear : ContinuousOn (fun x => m * (x - b)) (Set.Icc a b) := by
    have hconst : Continuous fun _ : ℝ => m := continuous_const
    have hsub : Continuous fun x : ℝ => x - b :=
      continuous_id.sub continuous_const
    exact (hconst.mul hsub).continuousOn
  have hcont_g : ContinuousOn g (Set.Icc a b) :=
    (hcont.sub hcont_const).sub hcont_linear
  have hdiff_const : DifferentiableOn ℝ (fun _ : ℝ => f b) (Set.Ioo a b) :=
    differentiableOn_const (c := f b) (s := Set.Ioo a b)
  have hdiff_linear : DifferentiableOn ℝ (fun x => m * (x - b)) (Set.Ioo a b) := by
    have hsub : Differentiable ℝ fun x : ℝ => x - b :=
      differentiable_id.sub_const b
    exact (hsub.const_mul m).differentiableOn
  have hdiff_g : DifferentiableOn ℝ g (Set.Ioo a b) :=
    (hdiff.sub hdiff_const).sub hdiff_linear
  obtain ⟨c, hc, hderivg⟩ :=
    rolle h₁ hcont_g hdiff_g (by simp [hga, hgb])
  have hderiv_f : DifferentiableAt ℝ f c :=
    hdiff.differentiableAt (isOpen_Ioo.mem_nhds hc)
  have hderiv_const_at : HasDerivAt (fun _ : ℝ => f b) 0 c := by
    simpa using (hasDerivAt_const c (f b))
  have hderiv_sub : HasDerivAt (fun x : ℝ => x - b) 1 c := by
    simpa using (hasDerivAt_id c).sub_const b
  have hderiv_linear_at : HasDerivAt (fun x : ℝ => m * (x - b)) m c := by
    simpa using (hderiv_sub.const_mul m)
  have hderivg' : deriv g c = deriv f c - m := by
    have h :=
      ((hderiv_f.hasDerivAt.sub hderiv_const_at).sub hderiv_linear_at).deriv
    simpa [g] using h
  have hfm : deriv f c = m := by
    have hzero : deriv f c - m = 0 := by
      simpa [hderivg'] using hderivg
    exact sub_eq_zero.mp hzero
  refine ⟨c, hc, ?_⟩
  calc
    f b - f a = m * (b - a) := by simp [hmul]
    _ = deriv f c * (b - a) := by simp [hfm]

/-- Theorem 4.2.5 (Cauchy's mean value theorem): If `f, φ : [a, b] → ℝ` are
continuous on the closed interval and differentiable on the open interval,
then some `c ∈ (a, b)` satisfies
`(f b - f a) * deriv φ c = deriv f c * (φ b - φ a)`. -/
theorem cauchy_mean_value_theorem
    {f φ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont_f : ContinuousOn f (Set.Icc a b))
    (hcont_φ : ContinuousOn φ (Set.Icc a b))
    (hdiff_f : DifferentiableOn ℝ f (Set.Ioo a b))
    (hdiff_φ : DifferentiableOn ℝ φ (Set.Ioo a b)) :
    ∃ c ∈ Set.Ioo a b,
      (f b - f a) * deriv φ c = deriv f c * (φ b - φ a) := by
  classical
  -- Auxiliary function for Rolle in Cauchy's MVT.
  let g : ℝ → ℝ := fun x => (f b - f a) * φ x - (φ b - φ a) * f x
  -- Helper: g has equal endpoint values.
  have hga : g a = g b := by
    dsimp [g]
    ring
  -- Helper: g is continuous on the closed interval.
  have hcont_g : ContinuousOn g (Set.Icc a b) := by
    have hcont1 :
        ContinuousOn (fun x => (f b - f a) * φ x) (Set.Icc a b) :=
      continuousOn_const.mul hcont_φ
    have hcont2 :
        ContinuousOn (fun x => (φ b - φ a) * f x) (Set.Icc a b) :=
      continuousOn_const.mul hcont_f
    simpa [g] using hcont1.sub hcont2
  -- Helper: g is differentiable on the open interval.
  have hdiff_g : DifferentiableOn ℝ g (Set.Ioo a b) := by
    have hdiff1 :
        DifferentiableOn ℝ (fun x => (f b - f a) * φ x) (Set.Ioo a b) :=
      hdiff_φ.const_mul (f b - f a)
    have hdiff2 :
        DifferentiableOn ℝ (fun x => (φ b - φ a) * f x) (Set.Ioo a b) :=
      hdiff_f.const_mul (φ b - φ a)
    simpa [g] using hdiff1.sub hdiff2
  obtain ⟨c, hc, hderivg⟩ := rolle hab hcont_g hdiff_g hga
  have hderiv_f : DifferentiableAt ℝ f c :=
    hdiff_f.differentiableAt (isOpen_Ioo.mem_nhds hc)
  have hderiv_φ : DifferentiableAt ℝ φ c :=
    hdiff_φ.differentiableAt (isOpen_Ioo.mem_nhds hc)
  -- Helper: derivative of g at c.
  have hderivg' :
      deriv g c =
        (f b - f a) * deriv φ c - (φ b - φ a) * deriv f c := by
    have h1 :
        HasDerivAt (fun x => (f b - f a) * φ x)
          ((f b - f a) * deriv φ c) c := by
      simpa using (hderiv_φ.hasDerivAt.const_mul (f b - f a))
    have h2 :
        HasDerivAt (fun x => (φ b - φ a) * f x)
          ((φ b - φ a) * deriv f c) c := by
      simpa using (hderiv_f.hasDerivAt.const_mul (φ b - φ a))
    have h := (h1.sub h2).deriv
    simpa [g] using h
  have hzero :
      (f b - f a) * deriv φ c - (φ b - φ a) * deriv f c = 0 := by
    simpa [hderivg'] using hderivg
  have hmain :
      (f b - f a) * deriv φ c = (φ b - φ a) * deriv f c :=
    sub_eq_zero.mp hzero
  refine ⟨c, hc, ?_⟩
  simpa [mul_comm] using hmain

/-- Proposition 4.2.6: If `I` is an interval and `f : I → ℝ` is differentiable
with `deriv f x = 0` for every `x ∈ I`, then `f` is constant on `I`. -/
lemma deriv_zero_on_interval_const {I : Set ℝ} (hI : Set.OrdConnected I) {f : ℝ → ℝ}
    (hdiff : DifferentiableOn ℝ f I) (hderiv : ∀ x ∈ I, deriv f x = 0) :
    ∀ {x y}, x ∈ I → y ∈ I → f x = f y := by
  have hconst :
      ∀ {x y}, x < y → x ∈ I → y ∈ I → f y = f x := by
    intro x y hxy hx hy
    have hsubset : Set.Icc x y ⊆ I := hI.out hx hy
    have hcont : ContinuousOn f (Set.Icc x y) :=
      (hdiff.continuousOn).mono hsubset
    have hdiff' : DifferentiableOn ℝ f (Set.Ioo x y) :=
      hdiff.mono (by
        intro z hz
        exact hsubset (Set.Ioo_subset_Icc_self hz))
    rcases mean_value_theorem hxy hcont hdiff' with ⟨c, hc, hsec⟩
    have hcI : c ∈ I := hsubset (Set.Ioo_subset_Icc_self hc)
    have hdc : deriv f c = 0 := hderiv c hcI
    have hzero : f y - f x = 0 := by simpa [hdc] using hsec
    exact sub_eq_zero.mp hzero
  intro x y hx hy
  rcases lt_trichotomy x y with hlt | hEq | hgt
  · exact (hconst hlt hx hy).symm
  · subst hEq; rfl
  · exact hconst hgt hy hx

/-- Proposition 4.2.7: For a differentiable real function on a nondegenerate
interval, the derivative is nonnegative everywhere exactly when the function is
increasing, and nonpositive everywhere exactly when the function is decreasing. -/
lemma increasingOn_iff_deriv_nonneg {I : Set ℝ} (hI : Set.OrdConnected I)
    (hInt : (interior I).Nonempty) {f : ℝ → ℝ} (hdiff : DifferentiableOn ℝ f I) :
    (MonotoneOn f I ↔ ∀ x ∈ I, 0 ≤ deriv f x) := by
  constructor
  · intro hmono x hx
    have hnonnegWithin : 0 ≤ derivWithin f I x :=
      (hmono.derivWithin_nonneg (x := x))
    by_cases hAt : DifferentiableAt ℝ f x
    · have hUD : UniqueDiffWithinAt ℝ I x :=
        uniqueDiffWithinAt_convex hI.convex hInt (subset_closure hx)
      have hderiv :
          derivWithin f I x = deriv f x := hAt.derivWithin hUD
      simpa [hderiv] using hnonnegWithin
    · have hzero : deriv f x = 0 := deriv_zero_of_not_differentiableAt hAt
      have hzero' : 0 ≤ deriv f x := by simp [hzero]
      exact hzero'
  · intro hderiv
    have hderiv_int : ∀ x ∈ interior I, 0 ≤ deriv f x := fun x hx =>
      hderiv x (interior_subset hx)
    have hcont : ContinuousOn f I := hdiff.continuousOn
    have hdiff_int : DifferentiableOn ℝ f (interior I) :=
      hdiff.mono interior_subset
    exact
      monotoneOn_of_deriv_nonneg hI.convex hcont hdiff_int hderiv_int

lemma decreasingOn_iff_deriv_nonpos {I : Set ℝ} (hI : Set.OrdConnected I)
    (hInt : (interior I).Nonempty) {f : ℝ → ℝ} (hdiff : DifferentiableOn ℝ f I) :
    (AntitoneOn f I ↔ ∀ x ∈ I, deriv f x ≤ 0) := by
  constructor
  · intro hant x hx
    have hnonposWithin : derivWithin f I x ≤ 0 :=
      (hant.derivWithin_nonpos (x := x))
    by_cases hAt : DifferentiableAt ℝ f x
    · have hUD : UniqueDiffWithinAt ℝ I x :=
        uniqueDiffWithinAt_convex hI.convex hInt (subset_closure hx)
      have hderiv : derivWithin f I x = deriv f x := hAt.derivWithin hUD
      simpa [hderiv] using hnonposWithin
    · have hzero : deriv f x = 0 := deriv_zero_of_not_differentiableAt hAt
      have hzero' : deriv f x ≤ 0 := by simp [hzero]
      exact hzero'
  · intro hderiv
    have hderiv_int : ∀ x ∈ interior I, deriv f x ≤ 0 := fun x hx =>
      hderiv x (interior_subset hx)
    have hcont : ContinuousOn f I := hdiff.continuousOn
    have hdiff_int : DifferentiableOn ℝ f (interior I) :=
      hdiff.mono interior_subset
    exact antitoneOn_of_deriv_nonpos hI.convex hcont hdiff_int hderiv_int

/-- Proposition 4.2.8:
* (i) If `I` is an interval and `f : I → ℝ` is differentiable with
  `deriv f x > 0` for every `x ∈ I`, then `f` is strictly increasing.
* (ii) If `I` is an interval and `f : I → ℝ` is differentiable with
  `deriv f x < 0` for every `x ∈ I`, then `f` is strictly decreasing. -/
lemma strictMonoOn_of_deriv_pos' {I : Set ℝ} (hI : Set.OrdConnected I)
    {f : ℝ → ℝ} (hdiff : DifferentiableOn ℝ f I)
    (hpos : ∀ x ∈ I, 0 < deriv f x) :
    StrictMonoOn f I := by
  have hpos_int : ∀ x ∈ interior I, 0 < deriv f x := fun x hx =>
    hpos x (interior_subset hx)
  have hcont : ContinuousOn f I := hdiff.continuousOn
  exact strictMonoOn_of_deriv_pos hI.convex hcont hpos_int

lemma strictAntiOn_of_deriv_neg' {I : Set ℝ} (hI : Set.OrdConnected I)
    {f : ℝ → ℝ} (hdiff : DifferentiableOn ℝ f I)
    (hneg : ∀ x ∈ I, deriv f x < 0) :
    StrictAntiOn f I := by
  have hneg_int : ∀ x ∈ interior I, deriv f x < 0 := fun x hx =>
    hneg x (interior_subset hx)
  have hcont : ContinuousOn f I := hdiff.continuousOn
  exact strictAntiOn_of_deriv_neg hI.convex hcont hneg_int

lemma mvt_le_of_deriv_nonpos {f : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hcont : ContinuousOn f (Set.Icc x y))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo x y))
    (hderiv : ∀ z ∈ Set.Ioo x y, deriv f z ≤ 0) :
    f y ≤ f x := by
  have hsub : f y - f x ≤ 0 := by
    obtain ⟨c, hc, hsec⟩ := mean_value_theorem hxy hcont hdiff
    have hmul : deriv f c * (y - x) ≤ 0 := by
      have hdc : deriv f c ≤ 0 := hderiv c hc
      have hpos : 0 ≤ y - x := sub_nonneg.mpr hxy.le
      exact mul_nonpos_of_nonpos_of_nonneg hdc hpos
    simpa [hsec] using hmul
  exact sub_nonpos.mp hsub

lemma mvt_ge_of_deriv_nonneg {f : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hcont : ContinuousOn f (Set.Icc x y))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo x y))
    (hderiv : ∀ z ∈ Set.Ioo x y, 0 ≤ deriv f z) :
    f x ≤ f y := by
  have hsub : 0 ≤ f y - f x := by
    obtain ⟨c, hc, hsec⟩ := mean_value_theorem hxy hcont hdiff
    have hmul : 0 ≤ deriv f c * (y - x) := by
      have hdc : 0 ≤ deriv f c := hderiv c hc
      have hpos : 0 ≤ y - x := sub_nonneg.mpr hxy.le
      exact mul_nonneg hdc hpos
    simpa [hsec] using hmul
  exact sub_nonneg.mp hsub

/-- Proposition 4.2.9: Let `f : (a, b) → ℝ` be continuous, let `c ∈ (a, b)`,
and assume `f` is differentiable on `(a, c)` and `(c, b)`.
* (i) If `deriv f x ≤ 0` for `x ∈ (a, c)` and `deriv f x ≥ 0` for `x ∈ (c, b)`,
then `f` has an absolute minimum at `c`.
* (ii) If `deriv f x ≥ 0` for `x ∈ (a, c)` and `deriv f x ≤ 0` for `x ∈ (c, b)`,
then `f` has an absolute maximum at `c`. -/
theorem absMinOf_deriv_nonpos_left_nonneg_right
    {f : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Set.Ioo a b)
    (hcont : ContinuousOn f (Set.Ioo a b))
    (hdiff₁ : DifferentiableOn ℝ f (Set.Ioo a c))
    (hdiff₂ : DifferentiableOn ℝ f (Set.Ioo c b))
    (hle : ∀ x ∈ Set.Ioo a c, deriv f x ≤ 0)
    (hge : ∀ x ∈ Set.Ioo c b, 0 ≤ deriv f x) :
    IsMinOn f (Set.Ioo a b) c := by
  intro x hx
  rcases lt_trichotomy x c with hxc | rfl | hcx
  · -- case `x < c`
    have hsubset : Set.Icc x c ⊆ Set.Ioo a b := by
      intro t ht
      exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hc.2⟩
    have hcont' : ContinuousOn f (Set.Icc x c) := hcont.mono hsubset
    have hsubset_diff : Set.Ioo x c ⊆ Set.Ioo a c := by
      intro z hz
      exact ⟨lt_trans hx.1 hz.1, hz.2⟩
    have hdiff' : DifferentiableOn ℝ f (Set.Ioo x c) :=
      hdiff₁.mono hsubset_diff
    have hderiv' : ∀ z ∈ Set.Ioo x c, deriv f z ≤ 0 := by
      intro z hz
      exact hle z ⟨lt_trans hx.1 hz.1, hz.2⟩
    exact mvt_le_of_deriv_nonpos hxc hcont' hdiff' hderiv'
  · -- case `x = c`
    simp
  · -- case `c < x`
    have hsubset : Set.Icc c x ⊆ Set.Ioo a b := by
      intro t ht
      exact ⟨lt_of_lt_of_le hc.1 ht.1, lt_of_le_of_lt ht.2 hx.2⟩
    have hcont' : ContinuousOn f (Set.Icc c x) := hcont.mono hsubset
    have hsubset_diff : Set.Ioo c x ⊆ Set.Ioo c b := by
      intro z hz
      exact ⟨hz.1, lt_trans hz.2 hx.2⟩
    have hdiff' : DifferentiableOn ℝ f (Set.Ioo c x) :=
      hdiff₂.mono hsubset_diff
    have hderiv' : ∀ z ∈ Set.Ioo c x, 0 ≤ deriv f z := by
      intro z hz
      exact hge z ⟨hz.1, lt_trans hz.2 hx.2⟩
    exact mvt_ge_of_deriv_nonneg hcx hcont' hdiff' hderiv'

theorem absMaxOf_deriv_nonneg_left_nonpos_right
    {f : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Set.Ioo a b)
    (hcont : ContinuousOn f (Set.Ioo a b))
    (hdiff₁ : DifferentiableOn ℝ f (Set.Ioo a c))
    (hdiff₂ : DifferentiableOn ℝ f (Set.Ioo c b))
    (hge : ∀ x ∈ Set.Ioo a c, 0 ≤ deriv f x)
    (hle : ∀ x ∈ Set.Ioo c b, deriv f x ≤ 0) :
    IsMaxOn f (Set.Ioo a b) c := by
  intro x hx
  rcases lt_trichotomy x c with hxc | rfl | hcx
  · -- case `x < c`
    have hsubset : Set.Icc x c ⊆ Set.Ioo a b := by
      intro t ht
      exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hc.2⟩
    have hcont' : ContinuousOn f (Set.Icc x c) := hcont.mono hsubset
    have hsubset_diff : Set.Ioo x c ⊆ Set.Ioo a c := by
      intro z hz
      exact ⟨lt_trans hx.1 hz.1, hz.2⟩
    have hdiff' : DifferentiableOn ℝ f (Set.Ioo x c) :=
      hdiff₁.mono hsubset_diff
    have hderiv' : ∀ z ∈ Set.Ioo x c, 0 ≤ deriv f z := by
      intro z hz
      exact hge z ⟨lt_trans hx.1 hz.1, hz.2⟩
    exact mvt_ge_of_deriv_nonneg hxc hcont' hdiff' hderiv'
  · -- case `x = c`
    simp
  · -- case `c < x`
    have hsubset : Set.Icc c x ⊆ Set.Ioo a b := by
      intro t ht
      exact ⟨lt_of_lt_of_le hc.1 ht.1, lt_of_le_of_lt ht.2 hx.2⟩
    have hcont' : ContinuousOn f (Set.Icc c x) := hcont.mono hsubset
    have hsubset_diff : Set.Ioo c x ⊆ Set.Ioo c b := by
      intro z hz
      exact ⟨hz.1, lt_trans hz.2 hx.2⟩
    have hdiff' : DifferentiableOn ℝ f (Set.Ioo c x) :=
      hdiff₂.mono hsubset_diff
    have hderiv' : ∀ z ∈ Set.Ioo c x, deriv f z ≤ 0 := by
      intro z hz
      exact hle z ⟨hz.1, lt_trans hz.2 hx.2⟩
    exact mvt_le_of_deriv_nonpos hcx hcont' hdiff' hderiv'

/-- Proposition 4.2.10:
* (i) If `f : [a, b) → ℝ` is continuous, differentiable on `(a, b)`, and
  `lim_{x → a} f' x = L`, then `f` is differentiable at `a` with `deriv f a = L`.
* (ii) If `f : (a, b] → ℝ` is continuous, differentiable on `(a, b)`, and
  `lim_{x → b} f' x = L`, then `f` is differentiable at `b` with `deriv f b = L`. -/
theorem deriv_at_left_endpoint_of_tendsto {f : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hlim : Tendsto (fun x => deriv f x) (𝓝[>] a) (𝓝 L)) :
    DifferentiableWithinAt ℝ f (Set.Icc a b) a ∧
      derivWithin f (Set.Icc a b) a = L := by
  have hcont' : ContinuousWithinAt f (Set.Ioo a b) a := by
    have hconta : ContinuousWithinAt f (Set.Icc a b) a :=
      hcont a ⟨le_rfl, hab.le⟩
    exact hconta.mono Set.Ioo_subset_Icc_self
  have hderiv_Ici : HasDerivWithinAt f L (Set.Ici a) a := by
    have hs : Set.Ioo a b ∈ 𝓝[>] a := Ioo_mem_nhdsGT hab
    exact hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hcont' hs hlim
  have hderiv_Icc : HasDerivWithinAt f L (Set.Icc a b) a := by
    refine hderiv_Ici.mono ?_
    intro x hx
    exact hx.1
  have hUD : UniqueDiffWithinAt ℝ (Set.Icc a b) a :=
    (uniqueDiffOn_Icc hab) _ ⟨le_rfl, hab.le⟩
  refine ⟨hderiv_Icc.differentiableWithinAt, ?_⟩
  exact hderiv_Icc.derivWithin hUD

theorem deriv_at_right_endpoint_of_tendsto {f : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hlim : Tendsto (fun x => deriv f x) (𝓝[<] b) (𝓝 L)) :
    DifferentiableWithinAt ℝ f (Set.Icc a b) b ∧
      derivWithin f (Set.Icc a b) b = L := by
  have hcont' : ContinuousWithinAt f (Set.Ioo a b) b := by
    have hcontb : ContinuousWithinAt f (Set.Icc a b) b :=
      hcont b ⟨hab.le, le_rfl⟩
    exact hcontb.mono Set.Ioo_subset_Icc_self
  have hderiv_Iic : HasDerivWithinAt f L (Set.Iic b) b := by
    have hs : Set.Ioo a b ∈ 𝓝[<] b := Ioo_mem_nhdsLT hab
    exact hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hcont' hs hlim
  have hderiv_Icc : HasDerivWithinAt f L (Set.Icc a b) b := by
    refine hderiv_Iic.mono ?_
    intro x hx
    exact hx.2
  have hUD : UniqueDiffWithinAt ℝ (Set.Icc a b) b :=
    (uniqueDiffOn_Icc hab) _ ⟨hab.le, le_rfl⟩
  refine ⟨hderiv_Icc.differentiableWithinAt, ?_⟩
  exact hderiv_Icc.derivWithin hUD

/-- The derivative within the closed interval at the left endpoint equals the usual
derivative when `f` is differentiable there. -/
lemma derivWithin_left_eq_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hfa : DifferentiableAt ℝ f a) (h₁ : a < b) :
    derivWithin f (Set.Icc a b) a = deriv f a := by
  have h := hfa.hasDerivAt
  have hwithin : HasDerivWithinAt f (deriv f a) (Set.Icc a b) a := by
    simpa [h.deriv] using h.hasDerivWithinAt (s := Set.Icc a b)
  have hUD :
      UniqueDiffWithinAt ℝ (Set.Icc a b) a :=
    (uniqueDiffOn_Icc h₁) _ ⟨le_rfl, h₁.le⟩
  exact hwithin.derivWithin hUD

/-- The derivative within the closed interval at the right endpoint equals the usual
derivative when `f` is differentiable there. -/
lemma derivWithin_right_eq_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hfb : DifferentiableAt ℝ f b) (h₁ : a < b) :
    derivWithin f (Set.Icc a b) b = deriv f b := by
  have h := hfb.hasDerivAt
  have hwithin : HasDerivWithinAt f (deriv f b) (Set.Icc a b) b := by
    simpa [h.deriv] using h.hasDerivWithinAt (s := Set.Icc a b)
  have hUD :
      UniqueDiffWithinAt ℝ (Set.Icc a b) b :=
    (uniqueDiffOn_Icc h₁) _ ⟨h₁.le, le_rfl⟩
  exact hwithin.derivWithin hUD

/-- Theorem 4.2.11 (Darboux): If `f : [a, b] → ℝ` is differentiable and `y`
lies strictly between `deriv f a` and `deriv f b`, then some `c ∈ (a, b)`
has `deriv f c = y`. -/
theorem darboux_deriv
    {f : ℝ → ℝ} {a b y : ℝ} (h₁ : a < b)
    (hdiff : DifferentiableOn ℝ f (Set.Icc a b))
    (ha : DifferentiableAt ℝ f a) (hb : DifferentiableAt ℝ f b)
    (hy : (deriv f a < y ∧ y < deriv f b) ∨ (deriv f a > y ∧ y > deriv f b)) :
    ∃ c ∈ Set.Ioo a b, deriv f c = y := by
  classical
  have hderiv :
      ∀ x ∈ Set.Icc a b,
        HasDerivWithinAt f (derivWithin f (Set.Icc a b) x) (Set.Icc a b) x := by
    intro x hx
    exact (hdiff x hx).hasDerivWithinAt
  rcases hy with hlt | hgt
  · have hlt' :
        derivWithin f (Set.Icc a b) a < y ∧ y < derivWithin f (Set.Icc a b) b := by
      simpa [derivWithin_left_eq_deriv ha h₁, derivWithin_right_eq_deriv hb h₁] using hlt
    obtain ⟨c, hc, hceq⟩ :=
      exists_hasDerivWithinAt_eq_of_gt_of_lt h₁.le hderiv hlt'.1 hlt'.2
    have hcIoo : c ∈ Set.Ioo a b := hc
    have hmem : Set.Icc a b ∈ 𝓝 c :=
      mem_of_superset (isOpen_Ioo.mem_nhds hcIoo) Set.Ioo_subset_Icc_self
    have hdiff_c :
        DifferentiableAt ℝ f c := hdiff.differentiableAt hmem
    have hderiv_eq : derivWithin f (Set.Icc a b) c = deriv f c := by
      have hUD :
          UniqueDiffWithinAt ℝ (Set.Icc a b) c :=
        uniqueDiffWithinAt_convex (convex_Icc a b)
          (by
            have : (Set.Ioo a b).Nonempty := by
              rcases exists_between h₁ with ⟨m, hm1, hm2⟩
              exact ⟨m, hm1, hm2⟩
            simpa [interior_Icc] using this)
          (subset_closure (Set.Ioo_subset_Icc_self hcIoo))
      simpa using hdiff_c.derivWithin hUD
    refine ⟨c, hcIoo, ?_⟩
    simpa [hderiv_eq] using hceq
  · have hgt' :
        derivWithin f (Set.Icc a b) a > y ∧ y > derivWithin f (Set.Icc a b) b := by
      simpa [derivWithin_left_eq_deriv ha h₁, derivWithin_right_eq_deriv hb h₁] using hgt
    obtain ⟨c, hc, hceq⟩ :=
      exists_hasDerivWithinAt_eq_of_lt_of_gt h₁.le hderiv hgt'.1 hgt'.2
    have hcIoo : c ∈ Set.Ioo a b := hc
    have hmem : Set.Icc a b ∈ 𝓝 c :=
      mem_of_superset (isOpen_Ioo.mem_nhds hcIoo) Set.Ioo_subset_Icc_self
    have hdiff_c :
        DifferentiableAt ℝ f c := hdiff.differentiableAt hmem
    have hderiv_eq : derivWithin f (Set.Icc a b) c = deriv f c := by
      have hUD :
          UniqueDiffWithinAt ℝ (Set.Icc a b) c :=
        uniqueDiffWithinAt_convex (convex_Icc a b)
          (by
            have : (Set.Ioo a b).Nonempty := by
              rcases exists_between h₁ with ⟨m, hm1, hm2⟩
              exact ⟨m, hm1, hm2⟩
            simpa [interior_Icc] using this)
          (subset_closure (Set.Ioo_subset_Icc_self hcIoo))
      simpa using hdiff_c.derivWithin hUD
    refine ⟨c, hcIoo, ?_⟩
    simpa [hderiv_eq] using hceq

/-- Example 4.2.12: the function `x ↦ (x * sin (1/x))^2` is differentiable on `ℝ`,
has derivative `0` at the origin, but its derivative is not continuous there. -/
noncomputable def oscillatorySquared (x : ℝ) : ℝ :=
  (x * Real.sin x⁻¹) ^ 2

lemma oscillatorySquared_abs_le_square (x : ℝ) :
    |oscillatorySquared x| ≤ x ^ 2 := by
  classical
  have hbound :
      |x * Real.sin x⁻¹| ≤ |x| := by
    have := Real.abs_sin_le_one x⁻¹
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left this (abs_nonneg x)
  have hxle :
      (x * Real.sin x⁻¹) ^ 2 ≤ x ^ 2 := by
    simpa [pow_two, sq_abs] using (sq_le_sq.mpr hbound)
  have hnonneg :
      0 ≤ (x * Real.sin x⁻¹) ^ 2 := sq_nonneg _
  simpa [oscillatorySquared, abs_of_nonneg hnonneg] using hxle

lemma hasDerivAt_oscillatorySquared_zero :
    HasDerivAt oscillatorySquared 0 0 := by
  classical
  have hsmall :
      (fun x : ℝ => oscillatorySquared x) =o[𝓝 0] fun x => x := by
    refine (Asymptotics.isLittleO_iff.2 ?_)
    intro ε hε
    have hball :
        {x : ℝ | |x| < ε} ∈ 𝓝 (0 : ℝ) := by
      simpa [Metric.ball, Real.dist_eq, sub_eq_add_neg] using
        Metric.ball_mem_nhds (0 : ℝ) hε
    refine Filter.mem_of_superset hball ?_
    intro x hxlt
    have hxabs : |x| < ε := hxlt
    have hxle : |x| ≤ ε := le_of_lt hxabs
    have hxnonneg : 0 ≤ |x| := abs_nonneg _
    have hx_sq :
        |x| ^ 2 ≤ ε * |x| := by
      have hxmul :=
        mul_le_mul_of_nonneg_left hxle hxnonneg
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hxmul
    have hosc :
        |oscillatorySquared x| ≤ |x| ^ 2 := by
      have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
      simpa [hsq] using oscillatorySquared_abs_le_square x
    exact le_trans hosc hx_sq
  refine
    (hasDerivAt_iff_isLittleO (f := oscillatorySquared) (f' := 0) (x := 0)).2 ?_
  simpa [oscillatorySquared, sub_eq_add_neg] using hsmall

lemma hasDerivAt_oscillatorySquared_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt oscillatorySquared
      (2 * Real.sin x⁻¹ *
        (x * Real.sin x⁻¹ - Real.cos x⁻¹)) x := by
  classical
  have h_inv :
      HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := by
    simpa using hasDerivAt_inv (x := x) hx
  have h_sin :
      HasDerivAt (fun y : ℝ => Real.sin y⁻¹)
        (-Real.cos x⁻¹ / x ^ 2) x := by
    have := (Real.hasDerivAt_sin x⁻¹).comp x h_inv
    simpa [Function.comp, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm,
      mul_assoc] using this
  have h_mul :
      HasDerivAt (fun y : ℝ => y * Real.sin y⁻¹)
        (Real.sin x⁻¹ - Real.cos x⁻¹ / x) x := by
    have h_id := hasDerivAt_id x
    have hx' : x ≠ 0 := hx
    have := h_id.mul h_sin
    simpa [Function.comp, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm,
      mul_assoc, sub_eq_add_neg, hx'] using this
  have h_pow :
      HasDerivAt (fun y : ℝ => (y * Real.sin y⁻¹) ^ 2)
        (2 * (x * Real.sin x⁻¹) *
          (Real.sin x⁻¹ - Real.cos x⁻¹ / x)) x := by
    simpa using (h_mul.pow 2)
  have hmain :
      2 * (x * Real.sin x⁻¹) *
          (Real.sin x⁻¹ - Real.cos x⁻¹ / x) =
        2 * Real.sin x⁻¹ *
          (x * Real.sin x⁻¹ - Real.cos x⁻¹) := by
    have hx' : x ≠ 0 := hx
    have hfirst :
        2 * (x * Real.sin x⁻¹) * Real.sin x⁻¹ =
          2 * Real.sin x⁻¹ * (x * Real.sin x⁻¹) := by
      simp [mul_comm, mul_left_comm]
    have hsecond :
        2 * (x * Real.sin x⁻¹) * (Real.cos x⁻¹ / x) =
          2 * Real.sin x⁻¹ * Real.cos x⁻¹ := by
      simp [div_eq_mul_inv, hx', mul_comm, mul_left_comm, mul_assoc]
    calc
      2 * (x * Real.sin x⁻¹) *
          (Real.sin x⁻¹ - Real.cos x⁻¹ / x)
          = 2 * (x * Real.sin x⁻¹) * Real.sin x⁻¹ -
              2 * (x * Real.sin x⁻¹) * (Real.cos x⁻¹ / x) := by
                simp [mul_sub]
      _ = 2 * Real.sin x⁻¹ * (x * Real.sin x⁻¹) -
            2 * Real.sin x⁻¹ * Real.cos x⁻¹ := by
          simp [hfirst, hsecond]
      _ = 2 * Real.sin x⁻¹ *
            (x * Real.sin x⁻¹ - Real.cos x⁻¹) := by
          simp [mul_sub, mul_comm, mul_left_comm]
  have hfinal :
      HasDerivAt (fun y : ℝ => (y * Real.sin y⁻¹) ^ 2)
        (2 * Real.sin x⁻¹ *
          (x * Real.sin x⁻¹ - Real.cos x⁻¹)) x :=
    by simpa [hmain] using h_pow
  simpa [oscillatorySquared] using hfinal

lemma differentiable_oscillatorySquared : Differentiable ℝ oscillatorySquared := by
  classical
  intro x
  by_cases hx : x = 0
  · simpa [hx] using
      hasDerivAt_oscillatorySquared_zero.differentiableAt
  · exact
      (hasDerivAt_oscillatorySquared_of_ne_zero hx).differentiableAt

lemma deriv_oscillatorySquared_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    deriv oscillatorySquared x =
      2 * Real.sin x⁻¹ * (x * Real.sin x⁻¹ - Real.cos x⁻¹) := by
  classical
  simpa using
    (hasDerivAt_oscillatorySquared_of_ne_zero hx).deriv

lemma deriv_oscillatorySquared_at_zero : deriv oscillatorySquared 0 = 0 := by
  simpa using
    hasDerivAt_oscillatorySquared_zero.deriv

lemma oscillatorySquared_isGlobalMin : IsMinOn oscillatorySquared Set.univ 0 := by
  intro x _
  have hnonneg :
      0 ≤ oscillatorySquared x := by
    simpa [oscillatorySquared] using
      (sq_nonneg (x * Real.sin x⁻¹))
  simpa [oscillatorySquared] using hnonneg

noncomputable def oscSeq₁ (n : ℕ) : ℝ :=
  1 / (Real.pi / 4 + (n : ℝ) * (2 * Real.pi))

noncomputable def oscSeq₂ (n : ℕ) : ℝ :=
  1 / (3 * Real.pi / 4 + (n : ℝ) * (2 * Real.pi))

lemma oscSeq₁_pos (n : ℕ) : 0 < oscSeq₁ n := by
  have hden :
      0 < Real.pi / 4 + (n : ℝ) * (2 * Real.pi) := by
    have hx :
        0 ≤ (n : ℝ) * (2 * Real.pi) :=
      mul_nonneg (Nat.cast_nonneg _) (by positivity)
    exact add_pos_of_pos_of_nonneg (by positivity) hx
  simpa [oscSeq₁] using one_div_pos.mpr hden

lemma oscSeq₂_pos (n : ℕ) : 0 < oscSeq₂ n := by
  have hden :
      0 < 3 * Real.pi / 4 + (n : ℝ) * (2 * Real.pi) := by
    have hx :
        0 ≤ (n : ℝ) * (2 * Real.pi) :=
      mul_nonneg (Nat.cast_nonneg _) (by positivity)
    exact add_pos_of_pos_of_nonneg (by positivity) hx
  simpa [oscSeq₂] using one_div_pos.mpr hden

lemma tendsto_nat_mul_add_const_atTop {a b : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (n : ℝ) * a + b) atTop atTop := by
  refine Filter.tendsto_atTop.mpr ?_
  intro A
  obtain ⟨N, hN⟩ := exists_nat_ge ((A - b) / a)
  have ha_ne : a ≠ 0 := ne_of_gt ha
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hN' : (A - b) / a ≤ (n : ℝ) :=
    le_trans hN (by exact_mod_cast hn)
  have hmul :
      A - b ≤ (n : ℝ) * a := by
    have := mul_le_mul_of_nonneg_right hN' (le_of_lt ha)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
      sub_eq_add_neg, ha_ne] using this
  have hfinal : A ≤ (n : ℝ) * a + b := by
    have := add_le_add_right hmul b
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
  exact hfinal

lemma oscSeq₁_tendsto_zero :
    Tendsto oscSeq₁ atTop (𝓝 (0 : ℝ)) := by
  have hden :
      Tendsto (fun n : ℕ => (n : ℝ) * (2 * Real.pi) + Real.pi / 4)
        atTop atTop :=
    tendsto_nat_mul_add_const_atTop (by positivity : 0 < 2 * Real.pi)
  have hInv :
      Tendsto (fun n : ℕ => ((n : ℝ) * (2 * Real.pi) + Real.pi / 4)⁻¹)
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hden
  have hfun :
      (fun n : ℕ =>
        ((n : ℝ) * (2 * Real.pi) + Real.pi / 4)⁻¹) = oscSeq₁ := by
    funext n
    simp [oscSeq₁, add_comm, one_div]
  simpa [hfun] using hInv

lemma oscSeq₂_tendsto_zero :
    Tendsto oscSeq₂ atTop (𝓝 (0 : ℝ)) := by
  have hden :
      Tendsto (fun n : ℕ => (n : ℝ) * (2 * Real.pi) + 3 * Real.pi / 4)
        atTop atTop :=
    tendsto_nat_mul_add_const_atTop (by positivity : 0 < 2 * Real.pi)
  have hInv :
      Tendsto (fun n : ℕ => ((n : ℝ) * (2 * Real.pi) + 3 * Real.pi / 4)⁻¹)
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hden
  have hfun :
      (fun n : ℕ =>
        ((n : ℝ) * (2 * Real.pi) + 3 * Real.pi / 4)⁻¹) = oscSeq₂ := by
    funext n
    simp [oscSeq₂, add_comm, one_div]
  simpa [hfun] using hInv

lemma sin_inv_oscSeq₁ (n : ℕ) :
    Real.sin (oscSeq₁ n)⁻¹ = Real.sqrt 2 / 2 := by
  have :=
    Real.sin_add_int_mul_two_pi (Real.pi / 4) (n : ℤ)
  simpa [oscSeq₁, Int.cast_ofNat, mul_comm, mul_left_comm, mul_assoc, one_div,
    Real.sin_pi_div_four] using this

lemma cos_inv_oscSeq₁ (n : ℕ) :
    Real.cos (oscSeq₁ n)⁻¹ = Real.sqrt 2 / 2 := by
  have :=
    Real.cos_add_int_mul_two_pi (Real.pi / 4) (n : ℤ)
  simpa [oscSeq₁, Int.cast_ofNat, mul_comm, mul_left_comm, mul_assoc, one_div,
    Real.cos_pi_div_four] using this

lemma sin_inv_oscSeq₂ (n : ℕ) :
    Real.sin (oscSeq₂ n)⁻¹ = Real.sqrt 2 / 2 := by
  have hsin_base :
      Real.sin (oscSeq₂ n)⁻¹ = Real.sin (3 * Real.pi / 4) := by
    simpa [oscSeq₂, Int.cast_ofNat, mul_comm, mul_left_comm, mul_assoc, one_div]
      using Real.sin_add_int_mul_two_pi (3 * Real.pi / 4) (n : ℤ)
  have hval :
      Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    have : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    calc
      Real.sin (3 * Real.pi / 4)
          = Real.sin (Real.pi / 4) := by
              simp [this, Real.sin_pi_sub]
      _ = Real.sqrt 2 / 2 := by
        simp [Real.sin_pi_div_four]
  exact hsin_base.trans hval

lemma cos_inv_oscSeq₂ (n : ℕ) :
    Real.cos (oscSeq₂ n)⁻¹ = -Real.sin (oscSeq₂ n)⁻¹ := by
  have hcos_base :
      Real.cos (oscSeq₂ n)⁻¹ = Real.cos (3 * Real.pi / 4) := by
    simpa [oscSeq₂, Int.cast_ofNat, mul_comm, mul_left_comm, mul_assoc, one_div]
      using Real.cos_add_int_mul_two_pi (3 * Real.pi / 4) (n : ℤ)
  have hsin_base :
      Real.sin (oscSeq₂ n)⁻¹ = Real.sin (3 * Real.pi / 4) := by
    simpa [oscSeq₂, Int.cast_ofNat, mul_comm, mul_left_comm, mul_assoc, one_div]
      using Real.sin_add_int_mul_two_pi (3 * Real.pi / 4) (n : ℤ)
  have hval :
      Real.cos (3 * Real.pi / 4) = -Real.sin (3 * Real.pi / 4) := by
    have : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    calc
      Real.cos (3 * Real.pi / 4)
          = -Real.cos (Real.pi / 4) := by
              simp [this, Real.cos_pi_sub]
      _ = -Real.sin (Real.pi / 4) := by
        simp [Real.cos_pi_div_four, Real.sin_pi_div_four]
      _ = -Real.sin (3 * Real.pi / 4) := by
        simp [this, Real.sin_pi_sub]
  have hsin_neg :
      -Real.sin (3 * Real.pi / 4) = -Real.sin (oscSeq₂ n)⁻¹ :=
    congrArg (fun t => -t) hsin_base.symm
  exact hcos_base.trans (hval.trans hsin_neg)

lemma deriv_oscillatorySquared_oscSeq₁ (n : ℕ) :
    deriv oscillatorySquared (oscSeq₁ n) = oscSeq₁ n - 1 := by
  classical
  have hneq : oscSeq₁ n ≠ 0 := ne_of_gt (oscSeq₁_pos n)
  have hderiv :=
    deriv_oscillatorySquared_of_ne_zero hneq
  have hsin :
      Real.sin (oscSeq₁ n)⁻¹ = Real.cos (oscSeq₁ n)⁻¹ := by
    simp [sin_inv_oscSeq₁, cos_inv_oscSeq₁]
  have hsq :
      2 * Real.sin (oscSeq₁ n)⁻¹ ^ 2 = (1 : ℝ) := by
    simpa [hsin, two_mul] using
      Real.sin_sq_add_cos_sq (oscSeq₁ n)⁻¹
  have hmain :
      2 * Real.sin (oscSeq₁ n)⁻¹ *
          (oscSeq₁ n * Real.sin (oscSeq₁ n)⁻¹ -
            Real.cos (oscSeq₁ n)⁻¹) =
        (2 * Real.sin (oscSeq₁ n)⁻¹ ^ 2) *
          (oscSeq₁ n - 1) := by
    have hdiff :
        oscSeq₁ n * Real.sin (oscSeq₁ n)⁻¹ -
            Real.cos (oscSeq₁ n)⁻¹ =
          Real.sin (oscSeq₁ n)⁻¹ * (oscSeq₁ n - 1) := by
      have hcalc :
          Real.sin (oscSeq₁ n)⁻¹ * (oscSeq₁ n - 1) =
            oscSeq₁ n * Real.sin (oscSeq₁ n)⁻¹ -
              Real.sin (oscSeq₁ n)⁻¹ := by
        ring
      simpa [hsin] using hcalc.symm
    calc
      2 * Real.sin (oscSeq₁ n)⁻¹ *
          (oscSeq₁ n * Real.sin (oscSeq₁ n)⁻¹ -
            Real.cos (oscSeq₁ n)⁻¹)
          = 2 * Real.sin (oscSeq₁ n)⁻¹ *
              (Real.sin (oscSeq₁ n)⁻¹ * (oscSeq₁ n - 1)) := by
                simp [hdiff]
      _ = (2 * Real.sin (oscSeq₁ n)⁻¹ ^ 2) *
            (oscSeq₁ n - 1) := by
          simp [pow_two, mul_comm, mul_left_comm]
  have hxval :
      deriv oscillatorySquared (oscSeq₁ n) =
        (2 * Real.sin (oscSeq₁ n)⁻¹ ^ 2) *
          (oscSeq₁ n - 1) := by
    simpa [hmain] using hderiv
  simp [hxval, hsq]

lemma deriv_oscillatorySquared_oscSeq₂ (n : ℕ) :
    deriv oscillatorySquared (oscSeq₂ n) = oscSeq₂ n + 1 := by
  classical
  have hneq : oscSeq₂ n ≠ 0 := ne_of_gt (oscSeq₂_pos n)
  have hderiv :=
    deriv_oscillatorySquared_of_ne_zero hneq
  have hcos :
      Real.cos (oscSeq₂ n)⁻¹ = -Real.sin (oscSeq₂ n)⁻¹ := cos_inv_oscSeq₂ n
  have hsq :
      2 * Real.sin (oscSeq₂ n)⁻¹ ^ 2 = (1 : ℝ) := by
    simpa [hcos, two_mul] using
      Real.sin_sq_add_cos_sq (oscSeq₂ n)⁻¹
  have hmain :
      2 * Real.sin (oscSeq₂ n)⁻¹ *
          (oscSeq₂ n * Real.sin (oscSeq₂ n)⁻¹ -
            Real.cos (oscSeq₂ n)⁻¹) =
        (2 * Real.sin (oscSeq₂ n)⁻¹ ^ 2) *
          (oscSeq₂ n + 1) := by
    have hdiff :
        oscSeq₂ n * Real.sin (oscSeq₂ n)⁻¹ -
            Real.cos (oscSeq₂ n)⁻¹ =
          Real.sin (oscSeq₂ n)⁻¹ * (oscSeq₂ n + 1) := by
      have hcalc :
          Real.sin (oscSeq₂ n)⁻¹ * (oscSeq₂ n + 1) =
            oscSeq₂ n * Real.sin (oscSeq₂ n)⁻¹ +
              Real.sin (oscSeq₂ n)⁻¹ := by
        ring
      simpa [hcos, sub_eq_add_neg, add_comm] using hcalc.symm
    calc
      2 * Real.sin (oscSeq₂ n)⁻¹ *
          (oscSeq₂ n * Real.sin (oscSeq₂ n)⁻¹ -
            Real.cos (oscSeq₂ n)⁻¹)
          = 2 * Real.sin (oscSeq₂ n)⁻¹ *
              (Real.sin (oscSeq₂ n)⁻¹ * (oscSeq₂ n + 1)) := by
                simp [hdiff]
      _ = (2 * Real.sin (oscSeq₂ n)⁻¹ ^ 2) *
            (oscSeq₂ n + 1) := by
          simp [pow_two, mul_comm, mul_left_comm]
  have hxval :
      deriv oscillatorySquared (oscSeq₂ n) =
        (2 * Real.sin (oscSeq₂ n)⁻¹ ^ 2) *
          (oscSeq₂ n + 1) := by
    simpa [hmain] using hderiv
  simp [hxval, hsq]

lemma deriv_oscillatorySquared_not_continuous_at_zero :
    ¬ ContinuousAt (fun x => deriv oscillatorySquared x) 0 := by
  classical
  intro hcont
  have hzero :
      deriv oscillatorySquared 0 = 0 :=
    deriv_oscillatorySquared_at_zero
  have hlim₀ :
      Tendsto (fun n => deriv oscillatorySquared (oscSeq₁ n))
        atTop (𝓝 (deriv oscillatorySquared 0)) :=
    (hcont.tendsto).comp oscSeq₁_tendsto_zero
  have hlim_neg :
      Tendsto (fun n => deriv oscillatorySquared (oscSeq₁ n))
        atTop (𝓝 (-1 : ℝ)) := by
    have hsub :
        Tendsto (fun n : ℕ => oscSeq₁ n - 1) atTop (𝓝 ((0 : ℝ) - 1)) :=
      oscSeq₁_tendsto_zero.sub tendsto_const_nhds
    convert hsub using 1
    · ext n
      simp [deriv_oscillatorySquared_oscSeq₁]
    · simp
  have hcontr :
      deriv oscillatorySquared 0 = -1 :=
    tendsto_nhds_unique hlim₀ hlim_neg
  have : (0 : ℝ) = -1 := by
    calc
      (0 : ℝ)
          = deriv oscillatorySquared 0 := by simp [hzero]
      _ = -1 := hcontr
  norm_num at this

lemma deriv_oscillatorySquared_sign_changes :
    ∀ ε > 0, ∃ x₁ x₂,
      x₁ ∈ Set.Ioo (-ε) ε ∧ x₂ ∈ Set.Ioo (-ε) ε ∧
      deriv oscillatorySquared x₁ < 0 ∧ deriv oscillatorySquared x₂ > 0 := by
  classical
  intro ε hε
  have hpos : 0 < min ε (1 : ℝ) := lt_min hε (by norm_num)
  have hx_small :
      ∀ᶠ n in Filter.atTop,
        |oscSeq₁ n| < min ε (1 : ℝ) := by
    have :=
      (oscSeq₁_tendsto_zero.eventually
        (Metric.ball_mem_nhds (0 : ℝ) hpos))
    simpa [Real.dist_eq] using this
  have hy_small :
      ∀ᶠ n in Filter.atTop,
        |oscSeq₂ n| < ε := by
    have :=
      (oscSeq₂_tendsto_zero.eventually
        (Metric.ball_mem_nhds (0 : ℝ) hε))
    simpa [Real.dist_eq] using this
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hx_small
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hy_small
  have hx_bound :
      |oscSeq₁ N₁| < min ε (1 : ℝ) :=
    hN₁ N₁ le_rfl
  have hy_bound :
      |oscSeq₂ N₂| < ε :=
    hN₂ N₂ le_rfl
  have hxpos : 0 < oscSeq₁ N₁ := oscSeq₁_pos N₁
  have hypos : 0 < oscSeq₂ N₂ := oscSeq₂_pos N₂
  have habs₁ : |oscSeq₁ N₁| = oscSeq₁ N₁ :=
    abs_of_nonneg (le_of_lt hxpos)
  have habs₂ : |oscSeq₂ N₂| = oscSeq₂ N₂ :=
    abs_of_nonneg (le_of_lt hypos)
  refine
    ⟨oscSeq₁ N₁, oscSeq₂ N₂, ?_, ?_, ?_, ?_⟩
  · have hxlt :
        oscSeq₁ N₁ < ε :=
      lt_of_lt_of_le (by simpa [habs₁] using hx_bound) (min_le_left _ _)
    exact ⟨(neg_lt_zero.mpr hε).trans hxpos, hxlt⟩
  · have hylt :
        oscSeq₂ N₂ < ε := by simpa [habs₂] using hy_bound
    exact ⟨(neg_lt_zero.mpr hε).trans hypos, hylt⟩
  · have hxlt :
        oscSeq₁ N₁ < 1 :=
      lt_of_lt_of_le (by simpa [habs₁] using hx_bound) (min_le_right _ _)
    have hxneg :
        oscSeq₁ N₁ - 1 < 0 :=
      sub_neg.mpr hxlt
    simpa [deriv_oscillatorySquared_oscSeq₁] using hxneg
  · have hypos' :
        0 < oscSeq₂ N₂ + 1 :=
      add_pos_of_pos_of_nonneg hypos (by norm_num)
    simpa [deriv_oscillatorySquared_oscSeq₂] using hypos'

end Section02
end Chap04
lemma oscSeq₁_ne_zero (n : ℕ) : oscSeq₁ n ≠ 0 :=
  ne_of_gt (oscSeq₁_pos n)

lemma oscSeq₂_ne_zero (n : ℕ) : oscSeq₂ n ≠ 0 :=
  ne_of_gt (oscSeq₂_pos n)
