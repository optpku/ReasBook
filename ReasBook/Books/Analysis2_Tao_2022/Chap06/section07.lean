/-
Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap06
section Section07

/-- Lemma 6.8: if `T : ℝ^n → ℝ^n` is a bijective linear transformation,
then its inverse map is also linear. -/
lemma linear_inverse_of_bijective_linear_map
    {n : ℕ}
    (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hT : Function.Bijective T) :
    ∃ Tinv : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ),
      (∀ x, Tinv (T x) = x) ∧ ∀ y, T (Tinv y) = y := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) := LinearEquiv.ofBijective T hT
  refine ⟨e.symm.toLinearMap, ?_⟩
  constructor
  · intro x
    change e.symm (e x) = x
    simpa using e.symm_apply_apply x
  · intro y
    change e (e.symm y) = y
    simpa using e.apply_symm_apply y

/-- Helper for Theorem 6.9: obtain `HasDerivAt f (deriv f x0) x0` from
differentiability of `f` on an open set containing `x0`. -/
lemma helperForTheorem_6_9_hasDerivAt_f_at_x0
    (f : ℝ → ℝ) (I : Set ℝ) (x0 : ℝ)
    (hI_open : IsOpen I)
    (hx0 : x0 ∈ I)
    (hdiff : DifferentiableOn ℝ f I) :
    HasDerivAt f (deriv f x0) x0 := by
  exact ((hdiff x0 hx0).differentiableAt (hI_open.mem_nhds hx0)).hasDerivAt

/-- Helper for Theorem 6.9: `f (g y) = y` holds in a neighborhood of `f x0`
because it holds on the open interval `J` containing `f x0`. -/
lemma helperForTheorem_6_9_eventually_right_inverse_near_y0
    (f g : ℝ → ℝ) (J : Set ℝ) (x0 : ℝ)
    (hJ_open : IsOpen J)
    (hy0 : f x0 ∈ J)
    (hright : Set.RightInvOn g f J) :
    ∀ᶠ y in nhds (f x0), f (g y) = y := by
  exact Filter.mem_of_superset (IsOpen.mem_nhds hJ_open hy0) fun y hy => hright hy

/-- Helper for Theorem 6.9: choose a closed interval around `x0` contained in `I`,
and mapped by `f` into `J`. -/
lemma helperForTheorem_6_9_localIntervalWithinIAndPreimageJ
    (f : ℝ → ℝ) (I J : Set ℝ) (x0 : ℝ)
    (hI_open : IsOpen I)
    (hx0 : x0 ∈ I)
    (hJ_open : IsOpen J)
    (hy0 : f x0 ∈ J)
    (hdiff : DifferentiableOn ℝ f I) :
    ∃ p q : ℝ,
      p < x0 ∧ x0 < q ∧
      Set.Icc p q ⊆ I ∧ Set.MapsTo f (Set.Icc p q) J := by
  have hfd : HasDerivAt f (deriv f x0) x0 :=
    helperForTheorem_6_9_hasDerivAt_f_at_x0 f I x0 hI_open hx0 hdiff
  have hcont : ContinuousAt f x0 := hfd.continuousAt
  have hI_nhds : I ∈ nhds x0 := hI_open.mem_nhds hx0
  have hpreJ_nhds : f ⁻¹' J ∈ nhds x0 := hcont.preimage_mem_nhds (hJ_open.mem_nhds hy0)
  have hInter_nhds : I ∩ (f ⁻¹' J) ∈ nhds x0 := Filter.inter_mem hI_nhds hpreJ_nhds
  obtain ⟨a, b, hx0_mem_Ioo, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hInter_nhds
  have hax0 : a < x0 := hx0_mem_Ioo.1
  have hx0b : x0 < b := hx0_mem_Ioo.2
  let p : ℝ := (a + x0) / 2
  let q : ℝ := (x0 + b) / 2
  have hap : a < p := by
    dsimp [p]
    linarith
  have hpx0 : p < x0 := by
    dsimp [p]
    linarith
  have hx0q : x0 < q := by
    dsimp [q]
    linarith
  have hqb : q < b := by
    dsimp [q]
    linarith
  have hIcc_subset_Ioo : Set.Icc p q ⊆ Set.Ioo a b := by
    intro x hx
    constructor
    · exact lt_of_lt_of_le hap hx.1
    · exact lt_of_le_of_lt hx.2 hqb
  have hIcc_subset_I : Set.Icc p q ⊆ I := by
    intro x hx
    exact (hab (hIcc_subset_Ioo hx)).1
  have hMaps_f : Set.MapsTo f (Set.Icc p q) J := by
    intro x hx
    exact (hab (hIcc_subset_Ioo hx)).2
  exact ⟨p, q, hpx0, hx0q, hIcc_subset_I, hMaps_f⟩

/-- Helper for Theorem 6.9: on the local closed interval, injective continuous `f`
is either strictly increasing or strictly decreasing. -/
lemma helperForTheorem_6_9_strictOrderOnLocalInterval
    (f : ℝ → ℝ) (I : Set ℝ) (p q : ℝ)
    (hpq : p ≤ q)
    (hinj : Set.InjOn f I)
    (hIcc_subset_I : Set.Icc p q ⊆ I)
    (hdiff : DifferentiableOn ℝ f I) :
    StrictMonoOn f (Set.Icc p q) ∨ StrictAntiOn f (Set.Icc p q) := by
  have hcontI : ContinuousOn f I := hdiff.continuousOn
  have hcontIcc : ContinuousOn f (Set.Icc p q) := hcontI.mono hIcc_subset_I
  have hinjIcc : Set.InjOn f (Set.Icc p q) := hinj.mono hIcc_subset_I
  exact ContinuousOn.strictMonoOn_of_injOn_Icc' hpq hcontIcc hinjIcc

/-- Helper for Theorem 6.9: the local image `f '' Icc p q` is a neighborhood of `f x0`. -/
lemma helperForTheorem_6_9_localImageNeighborhoodAt_y0
    (f : ℝ → ℝ) (p q x0 : ℝ)
    (hpx0 : p < x0)
    (hx0q : x0 < q)
    (hcontIcc : ContinuousOn f (Set.Icc p q))
    (horder : StrictMonoOn f (Set.Icc p q) ∨ StrictAntiOn f (Set.Icc p q)) :
    f '' Set.Icc p q ∈ nhds (f x0) := by
  have hpq : p ≤ q := le_of_lt (lt_trans hpx0 hx0q)
  have hp_mem : p ∈ Set.Icc p q := Set.left_mem_Icc.mpr hpq
  have hq_mem : q ∈ Set.Icc p q := Set.right_mem_Icc.mpr hpq
  have hx0_mem : x0 ∈ Set.Icc p q := ⟨le_of_lt hpx0, le_of_lt hx0q⟩
  rcases horder with hmono | hanti
  · have hImage : f '' Set.Icc p q = Set.Icc (f p) (f q) :=
      hcontIcc.image_Icc_of_monotoneOn hpq hmono.monotoneOn
    have hfp_lt_fx0 : f p < f x0 := hmono hp_mem hx0_mem hpx0
    have hfx0_lt_fq : f x0 < f q := hmono hx0_mem hq_mem hx0q
    have hNhds : Set.Icc (f p) (f q) ∈ nhds (f x0) := Icc_mem_nhds hfp_lt_fx0 hfx0_lt_fq
    simpa [hImage] using hNhds
  · have hImage : f '' Set.Icc p q = Set.Icc (f q) (f p) :=
      hcontIcc.image_Icc_of_antitoneOn hpq hanti.antitoneOn
    have hfq_lt_fx0 : f q < f x0 := hanti hx0_mem hq_mem hx0q
    have hfx0_lt_fp : f x0 < f p := hanti hp_mem hx0_mem hpx0
    have hNhds : Set.Icc (f q) (f p) ∈ nhds (f x0) := Icc_mem_nhds hfq_lt_fx0 hfx0_lt_fp
    simpa [hImage] using hNhds

/-- Helper for Theorem 6.9: order behavior of `g` on the local image, together with
the neighborhood property of `g '' (f '' Icc p q)`. -/
lemma helperForTheorem_6_9_orderBehaviorOf_g_on_localImage
    (f g : ℝ → ℝ) (I J : Set ℝ) (x0 p q : ℝ)
    (hpx0 : p < x0)
    (hx0q : x0 < q)
    (hIcc_subset_I : Set.Icc p q ⊆ I)
    (hMaps_f : Set.MapsTo f (Set.Icc p q) J)
    (hleft : ∀ ⦃x⦄, x ∈ I → f x ∈ J → g (f x) = x)
    (hright : Set.RightInvOn g f J)
    (horder : StrictMonoOn f (Set.Icc p q) ∨ StrictAntiOn f (Set.Icc p q)) :
    (MonotoneOn g (f '' Set.Icc p q) ∨ AntitoneOn g (f '' Set.Icc p q)) ∧
      g '' (f '' Set.Icc p q) ∈ nhds x0 := by
  let S : Set ℝ := f '' Set.Icc p q
  have hS_subset_J : S ⊆ J := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hMaps_f hx
  have hRightInvOnS : Set.RightInvOn g f S := by
    intro y hy
    exact hright (hS_subset_J hy)
  have hMaps_g : Set.MapsTo g S (Set.Icc p q) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxI : x ∈ I := hIcc_subset_I hx
    have hxJ : f x ∈ J := hMaps_f hx
    have hgf : g (f x) = x := hleft hxI hxJ
    simpa [hgf] using hx
  have hmonoOrAnti : MonotoneOn g S ∨ AntitoneOn g S := by
    rcases horder with hmono | hanti
    · exact Or.inl (Function.monotoneOn_of_rightInvOn_of_mapsTo hmono.monotoneOn hRightInvOnS hMaps_g)
    · exact Or.inr (Function.antitoneOn_of_rightInvOn_of_mapsTo hanti.antitoneOn hRightInvOnS hMaps_g)
  have hImage_subset : g '' S ⊆ Set.Icc p q := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact hMaps_g hy
  have hIcc_subset_image : Set.Icc p q ⊆ g '' S := by
    intro x hx
    have hxI : x ∈ I := hIcc_subset_I hx
    have hxJ : f x ∈ J := hMaps_f hx
    have hgf : g (f x) = x := hleft hxI hxJ
    refine ⟨f x, ?_, hgf⟩
    exact ⟨x, hx, rfl⟩
  have hImage_eq : g '' S = Set.Icc p q := Set.Subset.antisymm hImage_subset hIcc_subset_image
  have hImage_nhds : g '' S ∈ nhds x0 := by
    have hIcc_nhds : Set.Icc p q ∈ nhds x0 := Icc_mem_nhds hpx0 hx0q
    simpa [hImage_eq] using hIcc_nhds
  have hmonoOrAnti' : MonotoneOn g (f '' Set.Icc p q) ∨ AntitoneOn g (f '' Set.Icc p q) := by
    simpa [S] using hmonoOrAnti
  have hImage_nhds' : g '' (f '' Set.Icc p q) ∈ nhds x0 := by
    simpa [S] using hImage_nhds
  exact ⟨hmonoOrAnti', hImage_nhds'⟩

/-- Helper for Theorem 6.9: continuity of the inverse branch `g` at `f x0`. -/
lemma helperForTheorem_6_9_continuousAt_g_at_y0
    (f g : ℝ → ℝ) (I J : Set ℝ) (x0 : ℝ)
    (hinj : Set.InjOn f I)
    (hI_open : IsOpen I)
    (hI_interval : Convex ℝ I)
    (hx0 : x0 ∈ I)
    (hdiff : DifferentiableOn ℝ f I)
    (hJ_open : IsOpen J)
    (hy0 : f x0 ∈ J)
    (hMapsInv : Set.MapsTo g J I)
    (hleft : ∀ ⦃x⦄, x ∈ I → f x ∈ J → g (f x) = x)
    (hright : Set.RightInvOn g f J) :
    ContinuousAt g (f x0) := by
  obtain ⟨p, q, hpx0, hx0q, hIcc_subset_I, hMaps_f⟩ :=
    helperForTheorem_6_9_localIntervalWithinIAndPreimageJ
      f I J x0 hI_open hx0 hJ_open hy0 hdiff
  have hpq : p ≤ q := le_of_lt (lt_trans hpx0 hx0q)
  have hcontIcc : ContinuousOn f (Set.Icc p q) := (hdiff.continuousOn).mono hIcc_subset_I
  have horder :
      StrictMonoOn f (Set.Icc p q) ∨ StrictAntiOn f (Set.Icc p q) :=
    helperForTheorem_6_9_strictOrderOnLocalInterval
      f I p q hpq hinj hIcc_subset_I hdiff
  have hS_nhds : f '' Set.Icc p q ∈ nhds (f x0) :=
    helperForTheorem_6_9_localImageNeighborhoodAt_y0
      f p q x0 hpx0 hx0q hcontIcc horder
  have hOrderAndImage :
      (MonotoneOn g (f '' Set.Icc p q) ∨ AntitoneOn g (f '' Set.Icc p q)) ∧
        g '' (f '' Set.Icc p q) ∈ nhds x0 :=
    helperForTheorem_6_9_orderBehaviorOf_g_on_localImage
      f g I J x0 p q hpx0 hx0q hIcc_subset_I hMaps_f hleft hright horder
  have hgfx0 : g (f x0) = x0 := hleft hx0 hy0
  have hImage_nhds_gfx0 : g '' (f '' Set.Icc p q) ∈ nhds (g (f x0)) := by
    simpa [hgfx0] using hOrderAndImage.2
  rcases hOrderAndImage.1 with hmono | hanti
  · exact continuousAt_of_monotoneOn_of_image_mem_nhds hmono hS_nhds hImage_nhds_gfx0
  · have hmonoNeg : MonotoneOn (fun y => -g y) (f '' Set.Icc p q) := by
      intro y hy z hz hyz
      have hzy : g z ≤ g y := hanti hy hz hyz
      linarith
    have hnegImage :
        (fun y => -g y) '' (f '' Set.Icc p q) ∈
          nhds ((fun y => -g y) (f x0)) := by
      have hnegImage' :
          (fun t : ℝ => -t) '' (g '' (f '' Set.Icc p q)) ∈ nhds (-(g (f x0))) :=
        (Homeomorph.neg ℝ).isOpenMap.image_mem_nhds hImage_nhds_gfx0
      simpa [Set.image_image, Function.comp] using hnegImage'
    have hcontNeg : ContinuousAt (fun y => -g y) (f x0) :=
      continuousAt_of_monotoneOn_of_image_mem_nhds hmonoNeg hS_nhds hnegImage
    have hcontG : ContinuousAt (fun y => -(-g y)) (f x0) :=
      continuous_neg.continuousAt.comp hcontNeg
    simpa using hcontG

/-- Helper for Theorem 6.9: derivative of the inverse branch at `y0 = f x0`. -/
lemma helperForTheorem_6_9_hasDerivAt_g_at_y0
    (f g : ℝ → ℝ) (I J : Set ℝ) (x0 : ℝ)
    (hinj : Set.InjOn f I)
    (hI_open : IsOpen I)
    (hI_interval : Convex ℝ I)
    (hx0 : x0 ∈ I)
    (hdiff : DifferentiableOn ℝ f I)
    (hderiv_ne : deriv f x0 ≠ 0)
    (hJ_open : IsOpen J)
    (hy0 : f x0 ∈ J)
    (hMapsInv : Set.MapsTo g J I)
    (hleft : ∀ ⦃x⦄, x ∈ I → f x ∈ J → g (f x) = x)
    (hright : Set.RightInvOn g f J) :
    HasDerivAt g (deriv f x0)⁻¹ (f x0) := by
  have hcont : ContinuousAt g (f x0) :=
    helperForTheorem_6_9_continuousAt_g_at_y0
      f g I J x0 hinj hI_open hI_interval hx0 hdiff hJ_open hy0 hMapsInv hleft hright
  have hfd : HasDerivAt f (deriv f x0) x0 :=
    helperForTheorem_6_9_hasDerivAt_f_at_x0 f I x0 hI_open hx0 hdiff
  have hfg : ∀ᶠ y in nhds (f x0), f (g y) = y :=
    helperForTheorem_6_9_eventually_right_inverse_near_y0 f g J x0 hJ_open hy0 hright
  have hgfx0 : g (f x0) = x0 := hleft hx0 hy0
  have hfd_at_g : HasDerivAt f (deriv f x0) (g (f x0)) := by
    simpa [hgfx0] using hfd
  exact HasDerivAt.of_local_left_inverse hcont hfd_at_g hderiv_ne hfg

/-- Theorem 6.9 (Inverse function theorem in one variable): let `f : ℝ → ℝ` be injective
and differentiable on an open interval `I`, let `x₀ ∈ I` and set `y₀ = f x₀`.
Assume `deriv f x₀ ≠ 0`, and suppose `g` is the inverse of `f` on an open interval
`J` containing `y₀` (so `g (f x) = x` for `x ∈ I` and `f (g y) = y` for `y ∈ J`).
Then `g` is differentiable at `y₀` and `deriv g y₀ = 1 / deriv f x₀`. -/
theorem inverse_function_theorem_one_variable_6_9
    (f g : ℝ → ℝ) (I J : Set ℝ) (x0 : ℝ)
    (hinj : Set.InjOn f I)
    (hI_open : IsOpen I)
    (hI_interval : Convex ℝ I)
    (hx0 : x0 ∈ I)
    (hdiff : DifferentiableOn ℝ f I)
    (hderiv_ne : deriv f x0 ≠ 0)
    (hJ_open : IsOpen J)
    (hJ_interval : Convex ℝ J)
    (hy0 : f x0 ∈ J)
    (hMapsInv : Set.MapsTo g J I)
    (hleft : ∀ ⦃x⦄, x ∈ I → f x ∈ J → g (f x) = x)
    (hright : Set.RightInvOn g f J) :
    DifferentiableAt ℝ g (f x0) ∧ deriv g (f x0) = 1 / deriv f x0 := by
  have hgd : HasDerivAt g (deriv f x0)⁻¹ (f x0) :=
    helperForTheorem_6_9_hasDerivAt_g_at_y0
      f g I J x0 hinj hI_open hI_interval hx0 hdiff hderiv_ne hJ_open hy0 hMapsInv hleft hright
  constructor
  · exact hgd.differentiableAt
  · have hInv : (deriv f x0)⁻¹ = 1 / deriv f x0 := by
      rw [one_div]
    exact hgd.deriv.trans hInv

/-- Definition 6.15 (Local invertibility): a function `f : ℝ → ℝ` is locally invertible
near `x₀` if there exist open intervals `(a, b)` and `(c, d)` with `x₀ ∈ (a, b)` and
`f x₀ ∈ (c, d)` such that the restriction `f|(a,b) : (a,b) → (c,d)` is a bijection. -/
def LocallyInvertibleNear (f : ℝ → ℝ) (x0 : ℝ) : Prop :=
  ∃ a b c d : ℝ,
    a < x0 ∧ x0 < b ∧ c < f x0 ∧ f x0 < d ∧
    Set.BijOn f (Set.Ioo a b) (Set.Ioo c d)

/-- Theorem 6.10 (Inverse Function Theorem): let `E ⊆ ℝ^n` be open and let
`f : E → ℝ^n` be continuously differentiable on `E`. If `x₀ ∈ E` and
`f'(x₀)` is invertible (encoded by `fderiv ℝ f x₀ = f₀` for a linear equivalence `f₀`),
then there exist open sets `U ⊆ E` and `V ⊆ ℝ^n` with `x₀ ∈ U` and `f x₀ ∈ V`
such that `f` restricts to a bijection `U → V` with inverse `g : V → U`.
Moreover, `g` is differentiable at `y₀ = f x₀` and
`fderiv ℝ g y₀ = (f'(x₀))⁻¹`. -/
theorem inverse_function_theorem_several_variables_6_10
    {n : ℕ}
    {E : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → (Fin n → ℝ)}
    {x0 : Fin n → ℝ}
    (hE_open : IsOpen E)
    (hcont : ContDiffOn ℝ 1 f E)
    (hx0 : x0 ∈ E)
    (f0 : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hderiv : fderiv ℝ f x0 = (f0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) :
    ∃ U V : Set (Fin n → ℝ),
      IsOpen U ∧ IsOpen V ∧ x0 ∈ U ∧ U ⊆ E ∧ f x0 ∈ V ∧
      Set.BijOn f U V ∧
      ∃ g : (Fin n → ℝ) → (Fin n → ℝ),
        Set.MapsTo g V U ∧ Set.LeftInvOn g f U ∧ Set.RightInvOn g f V ∧
        DifferentiableAt ℝ g (f x0) ∧
        fderiv ℝ g (f x0) =
          ((f0.symm : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
            (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := by
  have hcontAt : ContDiffAt ℝ 1 f x0 :=
    hcont.contDiffAt (hE_open.mem_nhds hx0)
  have hfderivAt :
      HasFDerivAt f
        ((f0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) x0 := by
    have hfd0 : HasFDerivAt f (fderiv ℝ f x0) x0 :=
      (hcontAt.differentiableAt (by simp)).hasFDerivAt
    simpa [hderiv] using hfd0
  have hfStrict :
      HasStrictFDerivAt f
        ((f0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) x0 :=
    hcontAt.hasStrictFDerivAt' hfderivAt (by simp)
  let e : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ) :=
    hfStrict.toOpenPartialHomeomorph f
  let U : Set (Fin n → ℝ) := e.source ∩ E
  let V : Set (Fin n → ℝ) := e '' U
  have hx0_source : x0 ∈ e.source := by
    simpa [e] using hfStrict.mem_toOpenPartialHomeomorph_source (f := f)
  have hU_open : IsOpen U := by
    exact (e.open_source).inter hE_open
  have hU_subset_source : U ⊆ e.source := by
    exact Set.inter_subset_left
  have hV_open : IsOpen V := by
    exact e.isOpen_image_of_subset_source hU_open hU_subset_source
  have hx0_U : x0 ∈ U := by
    exact ⟨hx0_source, hx0⟩
  have hU_subset_E : U ⊆ E := by
    exact Set.inter_subset_right
  have hfx0_V : f x0 ∈ V := by
    have : e x0 ∈ V := ⟨x0, hx0_U, rfl⟩
    simpa [e] using this
  have hBijOn : Set.BijOn f U V := by
    have hInjOnU : Set.InjOn (e : (Fin n → ℝ) → (Fin n → ℝ)) U :=
      (e.injOn.mono hU_subset_source)
    have hBijOn_e : Set.BijOn (e : (Fin n → ℝ) → (Fin n → ℝ)) U V := by
      simpa [V] using hInjOnU.bijOn_image
    simpa [e] using hBijOn_e
  refine ⟨U, V, hU_open, hV_open, hx0_U, hU_subset_E, hfx0_V, hBijOn, ?_⟩
  refine ⟨e.symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hyV
    rcases hyV with ⟨x, hxU, rfl⟩
    have hx_source : x ∈ e.source := hU_subset_source hxU
    have hy_target : e x ∈ e.target := e.map_source hx_source
    refine ⟨e.symm_mapsTo hy_target, ?_⟩
    have hleft : e.symm (e x) = x := e.left_inv hx_source
    simpa [hleft] using hxU.2
  · intro x hxU
    have hx_source : x ∈ e.source := hU_subset_source hxU
    have hleft : e.symm (e x) = x := e.left_inv hx_source
    simpa [e] using hleft
  · intro y hyV
    rcases hyV with ⟨x, hxU, rfl⟩
    have hx_source : x ∈ e.source := hU_subset_source hxU
    have hy_target : e x ∈ e.target := e.map_source hx_source
    simpa [e] using e.right_inv hy_target
  · have hstrict_g :
        HasStrictFDerivAt e.symm
          (((f0.symm : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
            (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
          (f x0) := by
      simpa [e, HasStrictFDerivAt.localInverse_def] using
        (hfStrict.to_localInverse (f := f) (f' := f0) (a := x0))
    exact hstrict_g.differentiableAt
  · have hstrict_g :
        HasStrictFDerivAt e.symm
          (((f0.symm : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
            (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
          (f x0) := by
      simpa [e, HasStrictFDerivAt.localInverse_def] using
        (hfStrict.to_localInverse (f := f) (f' := f0) (a := x0))
    exact hstrict_g.hasFDerivAt.fderiv

end Section07
end Chap06
