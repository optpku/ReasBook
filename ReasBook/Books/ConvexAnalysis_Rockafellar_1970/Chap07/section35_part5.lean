/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part4

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

/-- Helper for Theorem 35.6: along any positive null sequence of admissible first-variable
steps, the moving second-variable slices converge pointwise on `D` back to the fixed slice
`z ↦ K u z`. -/
lemma helperForTheorem_35_6_movingSecondSlice_pointwiseTendstoOnD
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} (hu : u ∈ C)
    {τ : ℕ → ℝ}
    (hτpos : ∀ i, 0 < τ i) (hτle : ∀ i, τ i ≤ 1)
    (hτtendsto : Filter.Tendsto τ Filter.atTop (nhds (0 : ℝ)))
    {u' : Fin m → ℝ}
    (hu' : u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ))) :
    ∀ z ∈ D,
      Filter.Tendsto (fun i => K (u + τ i • u') z) Filter.atTop (nhds (K u z)) := by
  intro z hz
  let f : (Fin m → ℝ) → EReal := fun x => -K x z
  have hf : ConvexFunction f := by
    -- Fixing the second variable turns the first slice into a convex function after negation.
    simpa [f] using hK.1 z
  have hf_finite : ∀ x ∈ C, f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
    intro x hx
    have hxFinite : K x z ≠ (⊤ : EReal) ∧ K x z ≠ (⊥ : EReal) := hFinite x hx z hz
    exact ⟨by simpa [f] using hxFinite.2, by simpa [f] using hxFinite.1⟩
  have htoRealConv :
      ConvexOn ℝ C (fun x => (f x).toReal) := by
    -- Reusing the Chapter 24 `toReal` conversion avoids rebuilding the convexity argument.
    rcases
        helperForTheorem_5_24_8_toRealConvexOn_and_pointwiseTendsto
          (C := C) (hCconv := hC_conv) (f := f) hf hf_finite
          (fSeq := fun _ => f) (hfSeq := fun _ => hf) (hfSeq_finite := fun _ => hf_finite)
          (hpoint := by
            intro x hx
            exact
              (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => f x) Filter.atTop
                (nhds (f x)))) with
      ⟨_hCsubdom, _hCsubdomSeq, htoRealConv, _htoRealConvSeq, _htoRealPoint⟩
    exact htoRealConv
  have hnegCont : ContinuousOn (fun x => (f x).toReal) C := by
    -- Convex real-valued functions are continuous on the interior of their convex domain.
    simpa [hC_open.interior_eq] using htoRealConv.continuousOn_interior
  have hnegAt : ContinuousAt (fun x => (f x).toReal) u := by
    -- Since `u` lies in the open set `C`, continuity on `C` upgrades to ambient continuity at `u`.
    exact (continuousWithinAt_iff_continuousAt (hC_open.mem_nhds hu)).1 (hnegCont u hu)
  have hstep : Filter.Tendsto (fun i => u + τ i • u') Filter.atTop (nhds u) := by
    -- The admissible first-variable steps shrink back to the base point because `τ i → 0`.
    have hsmul :
        Filter.Tendsto (fun i => τ i • u') Filter.atTop (nhds ((0 : ℝ) • u')) := by
      simpa using hτtendsto.smul_const u'
    simpa using (tendsto_const_nhds.add hsmul)
  have hnegReal :
      Filter.Tendsto (fun i => (f (u + τ i • u')).toReal) Filter.atTop (nhds ((f u).toReal)) :=
    hnegAt.tendsto.comp hstep
  have hreal :
      Filter.Tendsto (fun i => (K (u + τ i • u') z).toReal) Filter.atTop
        (nhds ((K u z).toReal)) := by
    -- Negating the real-valued first slice recovers the original kernel values.
    simpa [f, EReal.toReal_neg] using hnegReal.neg
  have hstepFinite : ∀ i, K (u + τ i • u') z ≠ (⊤ : EReal) ∧ K (u + τ i • u') z ≠ (⊥ : EReal) := by
    intro i
    have huu' : u + u' ∈ C := hu'
    have huStep : u + τ i • u' ∈ C := by
      -- Convexity of `C` keeps the segment from `u` to `u + u'` inside `C`.
      have hrewrite : u + τ i • u' = (1 - τ i) • u + τ i • (u + u') := by
        ext j
        simp [smul_add]
        ring
      rw [hrewrite]
      exact hC_conv hu huu' (by linarith [hτle i]) (hτpos i).le (by linarith)
    exact hFinite (u + τ i • u') huStep z hz
  have htargetFinite : K u z ≠ (⊤ : EReal) ∧ K u z ≠ (⊥ : EReal) := hFinite u hu z hz
  have hcoe :
      Filter.Tendsto
        (fun i => (((K (u + τ i • u') z).toReal : ℝ) : EReal))
        Filter.atTop (nhds (((K u z).toReal : ℝ) : EReal)) :=
    helperForTheorem_5_24_8_tendsto_coe_of_tendsto hreal
  have hEqSeq :
      (fun i => K (u + τ i • u') z) =ᶠ[Filter.atTop]
        (fun i => (((K (u + τ i • u') z).toReal : ℝ) : EReal)) :=
    Filter.Eventually.of_forall fun i => (EReal.coe_toReal (hstepFinite i).1 (hstepFinite i).2).symm
  -- Replace the finite `EReal` values by their coerced real forms to finish the convergence.
  simpa [EReal.coe_toReal htargetFinite.1 htargetFinite.2] using
    Filter.Tendsto.congr' hEqSeq.symm hcoe

/-- Helper for Theorem 35.6: the Chapter 24 pointwise-limit theorem controls the limsup of the
upper directional derivatives of the moving second-variable slices. -/
lemma helperForTheorem_35_6_movingSecondSlice_limsup_upperDerivative
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    {τ : ℕ → ℝ}
    (hτpos : ∀ i, 0 < τ i) (hτle : ∀ i, τ i ≤ 1)
    (hτtendsto : Filter.Tendsto τ Filter.atTop (nhds (0 : ℝ)))
    {u' : Fin m → ℝ}
    (hu' : u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ)))
    (w : Fin n → ℝ) :
    Filter.limsup (fun i => upperDirectionalDerivativeAt (fun z => K (u + τ i • u') z) v w)
      Filter.atTop ≤ upperDirectionalDerivativeAt (K u) v w := by
  let f : (Fin n → ℝ) → EReal := K u
  let fSeq : ℕ → (Fin n → ℝ) → EReal := fun i z => K (u + τ i • u') z
  have hf : ConvexFunction f := by
    -- The fixed second-variable slice remains convex in the `v`-variable.
    simpa [f] using hK.2 u
  have hf_finite : ∀ z ∈ D, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal) := by
    intro z hz
    simpa [f] using hFinite u hu z hz
  have hfSeq : ∀ i, ConvexFunction (fSeq i) := by
    intro i
    -- Each translated second-variable slice is another global convex slice of `K`.
    simpa [fSeq] using hK.2 (u + τ i • u')
  have hfSeq_finite : ∀ i, ∀ z ∈ D, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal) := by
    intro i z hz
    have huu' : u + u' ∈ C := hu'
    have huStep : u + τ i • u' ∈ C := by
      -- The same segment computation keeps each translated first argument inside `C`.
      have hrewrite : u + τ i • u' = (1 - τ i) • u + τ i • (u + u') := by
        ext j
        simp [smul_add]
        ring
      rw [hrewrite]
      exact hC_conv hu huu' (by linarith [hτle i]) (hτpos i).le (by linarith)
    simpa [fSeq] using hFinite (u + τ i • u') huStep z hz
  have hpoint :
      ∀ z ∈ D, Filter.Tendsto (fun i => fSeq i z) Filter.atTop (nhds (f z)) := by
    intro z hz
    -- The previous helper packages the continuity argument for the moving first-variable base point.
    simpa [f, fSeq] using
      helperForTheorem_35_6_movingSecondSlice_pointwiseTendstoOnD
        (C := C) (D := D) (K := K) hC_open hC_conv hK hFinite hu
        hτpos hτle hτtendsto hu' z hz
  have hChapter24 :=
    convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
      (C := D) hD_open hD_conv hf hf_finite fSeq hfSeq hfSeq_finite hv
      (fun _ : ℕ => v) (by intro i; simpa)
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => v) Filter.atTop (nhds v))
      hpoint
  -- Specializing Chapter 24 to the constant direction sequence gives the desired limsup bound.
  simpa [f, fSeq] using
    hChapter24.1 w (fun _ : ℕ => w)
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => w) Filter.atTop (nhds w))

/-- Helper for Theorem 35.6: along any positive null sequence of admissible second-variable
steps, the moving first-variable slices converge pointwise on `C` back to the fixed slice
`x ↦ K x v`. -/
lemma helperForTheorem_35_6_movingFirstSlice_pointwiseTendstoOnC
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hD_open : IsOpen D) (hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {v : Fin n → ℝ} (hv : v ∈ D)
    {τ : ℕ → ℝ}
    (hτpos : ∀ i, 0 < τ i) (hτle : ∀ i, τ i ≤ 1)
    (hτtendsto : Filter.Tendsto τ Filter.atTop (nhds (0 : ℝ)))
    {v' : Fin n → ℝ}
    (hv' : v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ))) :
    ∀ z ∈ C,
      Filter.Tendsto (fun i => K z (v + τ i • v')) Filter.atTop (nhds (K z v)) := by
  intro z hz
  let g : (Fin n → ℝ) → EReal := K z
  have hg : ConvexFunction g := by
    -- Fixing the first variable leaves the second-variable slice convex.
    simpa [g] using hK.2 z
  have hg_finite : ∀ y ∈ D, g y ≠ (⊤ : EReal) ∧ g y ≠ (⊥ : EReal) := by
    intro y hy
    simpa [g] using hFinite z hz y hy
  have htoRealConv :
      ConvexOn ℝ D (fun y => (g y).toReal) := by
    -- The Chapter 24 `toReal` conversion gives a real convex slice on the finite domain `D`.
    rcases
        helperForTheorem_5_24_8_toRealConvexOn_and_pointwiseTendsto
          (C := D) (hCconv := hD_conv) (f := g) hg hg_finite
          (fSeq := fun _ => g) (hfSeq := fun _ => hg) (hfSeq_finite := fun _ => hg_finite)
          (hpoint := by
            intro y hy
            exact
              (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => g y) Filter.atTop
                (nhds (g y)))) with
      ⟨_hDsubdom, _hDsubdomSeq, htoRealConv, _htoRealConvSeq, _htoRealPoint⟩
    exact htoRealConv
  have hrealCont : ContinuousOn (fun y => (g y).toReal) D := by
    -- Real convexity gives continuity on the open domain `D`.
    simpa [hD_open.interior_eq] using htoRealConv.continuousOn_interior
  have hrealAt : ContinuousAt (fun y => (g y).toReal) v := by
    -- Since `v ∈ D` and `D` is open, the within-continuity is ambient continuity.
    exact (continuousWithinAt_iff_continuousAt (hD_open.mem_nhds hv)).1 (hrealCont v hv)
  have hstep : Filter.Tendsto (fun i => v + τ i • v') Filter.atTop (nhds v) := by
    -- The translated second-variable base points return to `v` because `τ i → 0`.
    have hsmul :
        Filter.Tendsto (fun i => τ i • v') Filter.atTop (nhds ((0 : ℝ) • v')) := by
      simpa using hτtendsto.smul_const v'
    simpa using (tendsto_const_nhds.add hsmul)
  have hreal :
      Filter.Tendsto (fun i => (K z (v + τ i • v')).toReal) Filter.atTop
        (nhds ((K z v).toReal)) := by
    -- Compose the real continuity of the slice with the shrinking translated base point.
    simpa [g] using hrealAt.tendsto.comp hstep
  have hstepFinite : ∀ i, K z (v + τ i • v') ≠ (⊤ : EReal) ∧ K z (v + τ i • v') ≠ (⊥ : EReal) := by
    intro i
    have hvv' : v + v' ∈ D := hv'
    have hvStep : v + τ i • v' ∈ D := by
      -- Convexity of `D` keeps the segment from `v` to `v + v'` inside `D`.
      have hrewrite : v + τ i • v' = (1 - τ i) • v + τ i • (v + v') := by
        ext j
        simp [smul_add]
        ring
      rw [hrewrite]
      exact hD_conv hv hvv' (by linarith [hτle i]) (hτpos i).le (by linarith)
    exact hFinite z hz (v + τ i • v') hvStep
  have htargetFinite : K z v ≠ (⊤ : EReal) ∧ K z v ≠ (⊥ : EReal) := hFinite z hz v hv
  have hcoe :
      Filter.Tendsto
        (fun i => (((K z (v + τ i • v')).toReal : ℝ) : EReal))
        Filter.atTop (nhds (((K z v).toReal : ℝ) : EReal)) :=
    helperForTheorem_5_24_8_tendsto_coe_of_tendsto hreal
  have hEqSeq :
      (fun i => K z (v + τ i • v')) =ᶠ[Filter.atTop]
        (fun i => (((K z (v + τ i • v')).toReal : ℝ) : EReal)) :=
    Filter.Eventually.of_forall fun i => (EReal.coe_toReal (hstepFinite i).1 (hstepFinite i).2).symm
  -- Replace the finite `EReal` values by their coerced real forms to finish the convergence.
  simpa [EReal.coe_toReal htargetFinite.1 htargetFinite.2] using
    Filter.Tendsto.congr' hEqSeq.symm hcoe

/-- Helper for Theorem 35.6: the Chapter 24 pointwise-limit theorem also controls the limsup of
the upper directional derivatives of the moving first-variable slices after negation. -/
lemma helperForTheorem_35_6_movingFirstSlice_limsup_upperDerivative
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    {τ : ℕ → ℝ}
    (hτpos : ∀ i, 0 < τ i) (hτle : ∀ i, τ i ≤ 1)
    (hτtendsto : Filter.Tendsto τ Filter.atTop (nhds (0 : ℝ)))
    {v' : Fin n → ℝ}
    (hv' : v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ)))
    (w : Fin m → ℝ) :
    Filter.limsup (fun i => upperDirectionalDerivativeAt (fun x => -K x (v + τ i • v')) u w)
      Filter.atTop ≤ upperDirectionalDerivativeAt (fun x => -K x v) u w := by
  let f : (Fin m → ℝ) → EReal := fun x => -K x v
  let fSeq : ℕ → (Fin m → ℝ) → EReal := fun i x => -K x (v + τ i • v')
  have hf : ConvexFunction f := by
    -- Fixing the second variable turns the first slice into a convex function after negation.
    simpa [f] using hK.1 v
  have hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal) := by
    intro z hz
    have hzFinite : K z v ≠ (⊤ : EReal) ∧ K z v ≠ (⊥ : EReal) := hFinite z hz v hv
    exact ⟨by simpa [f] using hzFinite.2, by simpa [f] using hzFinite.1⟩
  have hfSeq : ∀ i, ConvexFunction (fSeq i) := by
    intro i
    -- Each moved first-variable slice is again convex after negation.
    simpa [fSeq] using hK.1 (v + τ i • v')
  have hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal) := by
    intro i z hz
    have hvv' : v + v' ∈ D := hv'
    have hvStep : v + τ i • v' ∈ D := by
      -- Convexity of `D` keeps the translated second argument inside the finite domain.
      have hrewrite : v + τ i • v' = (1 - τ i) • v + τ i • (v + v') := by
        ext j
        simp [smul_add]
        ring
      rw [hrewrite]
      exact hD_conv hv hvv' (by linarith [hτle i]) (hτpos i).le (by linarith)
    have hzFinite : K z (v + τ i • v') ≠ (⊤ : EReal) ∧ K z (v + τ i • v') ≠ (⊥ : EReal) :=
      hFinite z hz (v + τ i • v') hvStep
    exact ⟨by simpa [fSeq] using hzFinite.2, by simpa [fSeq] using hzFinite.1⟩
  have hpoint :
      ∀ z ∈ C, Filter.Tendsto (fun i => fSeq i z) Filter.atTop (nhds (f z)) := by
    intro z hz
    have hzPoint :
        Filter.Tendsto (fun i => K z (v + τ i • v')) Filter.atTop (nhds (K z v)) :=
      helperForTheorem_35_6_movingFirstSlice_pointwiseTendstoOnC
        (C := C) (D := D) (K := K) hD_open hD_conv hK hFinite hv
        hτpos hτle hτtendsto hv' z hz
    -- Negating the convergent kernel values gives the pointwise convergence for the convex slices.
    simpa [f, fSeq] using hzPoint.neg
  have hChapter24 :=
    convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
      (C := C) hC_open hC_conv hf hf_finite fSeq hfSeq hfSeq_finite hu
      (fun _ : ℕ => u) (fun _ => hu)
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => u) Filter.atTop (nhds u))
      hpoint
  -- Specializing Chapter 24 to the constant direction sequence gives the symmetric limsup bound.
  simpa [f, fSeq] using
    hChapter24.1 w (fun _ : ℕ => w)
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => w) Filter.atTop (nhds w))

/-- Helper for Theorem 35.6: convexity of the translated second slice bounds its upper
directional derivative by the corresponding one-step mixed second-variable increment. -/
lemma helperForTheorem_35_6_upperDirectionalDerivative_le_fixedStepQuotient
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf : ConvexFunction f)
    {x y : Fin n → ℝ} {t : ℝ}
    (hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (ht : 0 < t) :
    upperDirectionalDerivativeAt f x y ≤ directionalDifferenceQuotientAt f x y t := by
  let g : (Fin n → ℝ) → EReal := fun w => directionalDifferenceQuotientAt f x w t
  have hxZeroFinite : f (x + t • (0 : Fin n → ℝ)) ≠ (⊤ : EReal) ∧
      f (x + t • (0 : Fin n → ℝ)) ≠ (⊥ : EReal) := by
    simpa using hxFinite
  have hgConv : ConvexFunction g := by
    -- The fixed-step secant quotient is convex in the direction variable.
    exact helperForTheorem_5_24_9_secantQuotient_convex (f := f) hproper hf hxFinite ht
  have hgZeroFinite : g 0 ≠ (⊤ : EReal) ∧ g 0 ≠ (⊥ : EReal) := by
    -- At direction `0`, the secant quotient only sees the finite base value `f x`.
    simpa [g] using
      (helperForTheorem_5_24_9_secantQuotient_finite
        (f := f) (x := x) (u := (0 : Fin n → ℝ)) hxFinite hxZeroFinite ht)
  rcases convex_directionalDerivative_monotone_exists_and_sublinear g hgConv 0 hgZeroFinite with
    ⟨hdirG, _hposG, _hconvG, _hzeroG, _hsymmG⟩
  have hq1 :
      upperDirectionalDerivativeAt g 0 y ≤ directionalDifferenceQuotientAt g 0 y 1 := by
    -- The derivative is the infimum of all positive-step quotients, so the concrete step `1`
    -- is an upper bound.
    exact
      helperForProposition_5_24_2_iterated_upperDerivative_le_of_quotientAt_one
        ((hdirG y).2.2)
  have htransport :
      upperDirectionalDerivativeAt g 0 y = upperDirectionalDerivativeAt f x y := by
    -- Differentiating the secant quotient at direction `0` transports back to the original base
    -- point `x`.
    simpa [g] using
      (helperForTheorem_5_24_9_secantQuotient_derivative_transport
        (f := f) hproper hf (x := x) (u := (0 : Fin n → ℝ)) (z := y) (t := t)
        hxFinite hxZeroFinite ht)
  have hqTransport :
      directionalDifferenceQuotientAt g 0 y 1 = directionalDifferenceQuotientAt f x y t := by
    -- The `λ = 1` quotient of the secant quotient is exactly the original step-`t` quotient.
    simpa [g] using
      (helperForTheorem_5_24_9_secantQuotient_pointwiseDifferenceQuotient_transport
        (f := f) (x := x) (u := (0 : Fin n → ℝ)) (z := y) (t := t) (lam := 1)
        hxFinite ht (by norm_num : 0 < (1 : ℝ)))
  calc
    upperDirectionalDerivativeAt f x y = upperDirectionalDerivativeAt g 0 y := htransport.symm
    _ ≤ directionalDifferenceQuotientAt g 0 y 1 := hq1
    _ = directionalDifferenceQuotientAt f x y t := hqTransport

/-- Helper for Theorem 35.6: convexity of the translated second slice bounds its upper
directional derivative by the corresponding one-step mixed second-variable increment. -/
lemma helperForTheorem_35_6_movingSecondDerivative_le_mixedSecondIncrement
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (_hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    {t : ℝ} (ht_pos : 0 < t) (ht_le : t ≤ 1)
    {u' : Fin m → ℝ} {v' : Fin n → ℝ}
    (hu' : u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ)))
    (_hv' : v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ))) :
    upperDirectionalDerivativeAt (fun z => K (u + t • u') z) v v' ≤
      ((K (u + t • u') (v + t • v') - K (u + t • u') v) / (t : EReal)) := by
  let x : Fin m → ℝ := u + t • u'
  have hx_mem : x ∈ C := by
    have huOne : u + u' ∈ C := hu'
    have hx_eq : x = (1 - t) • u + t • (u + u') := by
      ext i
      simp [x]
      ring
    -- Convexity keeps the translated first variable inside `C` for every `0 < t ≤ 1`.
    rw [hx_eq]
    exact hC_conv hu huOne (by linarith) (le_of_lt ht_pos) (by linarith)
  rcases
      helperForTheorem_35_6_secondSlice_directionalDerivativeData
        (C := C) (D := D) (K := K)
        hC_open hD_open hK hFinite (u := x) (v := v) hx_mem hv with
    ⟨hproper, _hDproper, _hPos, _hConv, _hZero, _hFiniteDir⟩
  let f : (Fin n → ℝ) → EReal := fun z => K x z
  have hf : ConvexFunction f := by
    -- Fixing the translated first variable preserves convexity in the second variable.
    simpa [f] using hK.2 x
  have hfv : f v ≠ (⊤ : EReal) ∧ f v ≠ (⊥ : EReal) := by
    -- The translated base point still lies in the finite open patch.
    simpa [f] using hFinite x hx_mem v hv
  -- Apply the generic fixed-step convex-slice bound to the moved second-variable slice.
  simpa [f, x, directionalDifferenceQuotientAt] using
    (helperForTheorem_35_6_upperDirectionalDerivative_le_fixedStepQuotient
      (f := f) hproper hf (x := v) (y := v') (t := t) hfv ht_pos)

/-- Helper for Theorem 35.6: convexity of the translated negated first slice bounds the mixed
first-variable increment above by the negative translated upper directional derivative. -/
lemma helperForTheorem_35_6_mixedFirstIncrement_le_negMovingFirstDerivative
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    {t : ℝ} (ht_pos : 0 < t) (ht_le : t ≤ 1)
    {u' : Fin m → ℝ} {v' : Fin n → ℝ}
    (hu' : u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ)))
    (hv' : v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ))) :
    ((K (u + t • u') (v + t • v') - K u (v + t • v')) / (t : EReal)) ≤
      -upperDirectionalDerivativeAt (fun x => -K x (v + t • v')) u u' := by
  let y : Fin n → ℝ := v + t • v'
  have hy_mem : y ∈ D := by
    have hvOne : v + v' ∈ D := hv'
    have hy_eq : y = (1 - t) • v + t • (v + v') := by
      ext i
      simp [y]
      ring
    -- Convexity keeps the translated second variable inside `D` for every `0 < t ≤ 1`.
    rw [hy_eq]
    exact hD_conv hv hvOne (by linarith) (le_of_lt ht_pos) (by linarith)
  rcases
      helperForTheorem_35_6_firstSlice_directionalDerivativeData
        (C := C) (D := D) (K := K)
        hC_open hD_open hK hFinite (u := u) (v := y) hu hy_mem with
    ⟨hproper, _hDproper, _hPos, _hConv, _hZero, _hFiniteDir⟩
  let f : (Fin m → ℝ) → EReal := fun x => -K x y
  have hf : ConvexFunction f := by
    -- Fixing the translated second variable preserves convexity after negating the first slice.
    simpa [f] using hK.1 y
  have hfu : f u ≠ (⊤ : EReal) ∧ f u ≠ (⊥ : EReal) := by
    have hbase : K u y ≠ (⊤ : EReal) ∧ K u y ≠ (⊥ : EReal) := hFinite u hu y hy_mem
    -- Negation swaps the `⊤` and `⊥` exclusions at the base point.
    exact ⟨by simpa [f] using hbase.2, by simpa [f] using hbase.1⟩
  have hbound :
      upperDirectionalDerivativeAt f u u' ≤ directionalDifferenceQuotientAt f u u' t :=
    helperForTheorem_35_6_upperDirectionalDerivative_le_fixedStepQuotient
      (f := f) hproper hf (x := u) (y := u') (t := t) hfu ht_pos
  have huStep : u + t • u' ∈ C := by
    have huOne : u + u' ∈ C := hu'
    have huStep_eq : u + t • u' = (1 - t) • u + t • (u + u') := by
      ext i
      simp
      ring
    -- Convexity keeps the translated first variable inside `C` for every `0 < t ≤ 1`.
    rw [huStep_eq]
    exact hC_conv hu huOne (by linarith) (le_of_lt ht_pos) (by linarith)
  have hfStep : f (u + t • u') ≠ (⊤ : EReal) ∧ f (u + t • u') ≠ (⊥ : EReal) := by
    have hbaseStep : K (u + t • u') y ≠ (⊤ : EReal) ∧ K (u + t • u') y ≠ (⊥ : EReal) :=
      hFinite (u + t • u') huStep y hy_mem
    -- Negation swaps the `⊤` and `⊥` exclusions at the translated first-variable point.
    exact ⟨by simpa [f] using hbaseStep.2, by simpa [f] using hbaseStep.1⟩
  have hleft :
      -directionalDifferenceQuotientAt f u u' t =
        ((K (u + t • u') y - K u y) / (t : EReal)) := by
    -- Rewrite the mixed first-variable increment as the negative secant quotient of the convex
    -- slice `f`.
    rw [directionalDifferenceQuotientAt, EReal.div_eq_inv_mul, neg_mul_eq_mul_neg]
    rw [EReal.neg_sub (Or.inl hfStep.2) (Or.inl hfStep.1)]
    rw [← EReal.div_eq_inv_mul]
    simp [f, sub_eq_add_neg]
  -- Replacing the mixed increment by the negative secant quotient lets the EReal negation lemma
  -- reverse the proved convex-slice bound.
  rw [← hleft]
  exact (EReal.neg_le_neg_iff).2 hbound

/-- Helper for Theorem 35.6: once each translated witness pair admits scalar upper and lower
bounds for the scaled mixed quotients, the whole quotient family is pointwise bounded on
`CU × DV`. -/
lemma helperForTheorem_35_6_pointwiseBounded_scaledQuotients_onTranslatedDomains
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {CU : Set (Fin m → ℝ)} {DV : Set (Fin n → ℝ)}
    {τ : ℕ → ℝ}
    (hUpper :
      ∀ {u' : Fin m → ℝ} {v' : Fin n → ℝ}, u' ∈ CU → v' ∈ DV →
        ∃ M : ℝ, ∀ i,
          (saddleDirectionalDifferenceQuotientAt K u v u' v' (τ i)).toReal ≤ M)
    (hLower :
      ∀ {u' : Fin m → ℝ} {v' : Fin n → ℝ}, u' ∈ CU → v' ∈ DV →
        ∃ m0 : ℝ, ∀ i,
          m0 ≤ (saddleDirectionalDifferenceQuotientAt K u v u' v' (τ i)).toReal) :
    Function.PointwiseBoundedFamilyOn
      (fun i => Function.uncurry fun u' v' =>
        (saddleDirectionalDifferenceQuotientAt K u v u' v' (τ i)).toReal)
      (CU ×ˢ DV) := by
  intro p hp
  rcases hUpper hp.1 hp.2 with ⟨M, hM⟩
  rcases hLower hp.1 hp.2 with ⟨m0, hm0⟩
  -- Bound the entire range by a closed ball centered at `0` using the two one-sided estimates.
  refine
    (Metric.isBounded_iff_subset_closedBall
      (s := Set.range fun i : ℕ =>
        (saddleDirectionalDifferenceQuotientAt K u v p.1 p.2 (τ i)).toReal)
      (c := (0 : ℝ))).2 ?_
  refine ⟨max |m0| |M|, ?_⟩
  rintro x ⟨i, rfl⟩
  let q : ℝ := (saddleDirectionalDifferenceQuotientAt K u v p.1 p.2 (τ i)).toReal
  have hqLower : m0 ≤ q := hm0 i
  have hqUpper : q ≤ M := hM i
  have hqBound : |q| ≤ max |m0| |M| := by
    by_cases hqNonneg : 0 ≤ q
    · -- On the nonnegative branch, the upper bound controls the absolute value.
      rw [abs_of_nonneg hqNonneg]
      exact le_max_of_le_right (le_trans hqUpper (le_abs_self M))
    · -- On the negative branch, the lower bound controls the absolute value after negation.
      have hqNeg : q < 0 := lt_of_not_ge hqNonneg
      rw [abs_of_neg hqNeg]
      have hneg_q_le : -q ≤ -m0 := by linarith
      exact le_max_of_le_left (le_trans hneg_q_le (neg_le_abs m0))
  -- Convert the absolute-value estimate into closed-ball membership.
  simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs, q] using hqBound

/-- Helper for Theorem 35.6: on every short admissible step, the mixed quotient splits exactly
into either axis quotient plus the corresponding moved one-variable increment. -/
lemma helperForTheorem_35_6_mixedQuotient_eq_axisPlusMovedIncrements
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    {t : ℝ} (ht_pos : 0 < t) (ht_le : t ≤ 1)
    {u' : Fin m → ℝ} {v' : Fin n → ℝ}
    (hu' : u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ)))
    (hv' : v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ))) :
    let mixedQ :=
      (saddleDirectionalDifferenceQuotientAt K u v u' v' t).toReal
    let firstAxisQ :=
      (((K (u + t • u') v - K u v) / (t : EReal)).toReal : ℝ)
    let secondAxisQ :=
      (((K u (v + t • v') - K u v) / (t : EReal)).toReal : ℝ)
    let movedFirstQ :=
      (((K (u + t • u') (v + t • v') - K u (v + t • v')) / (t : EReal)).toReal : ℝ)
    let movedSecondQ :=
      (((K (u + t • u') (v + t • v') - K (u + t • u') v) / (t : EReal)).toReal : ℝ)
    mixedQ = firstAxisQ + movedSecondQ ∧ mixedQ = secondAxisQ + movedFirstQ := by
  dsimp
  have hMixedFinite :
      K (u + t • u') (v + t • v') ≠ (⊤ : EReal) ∧
        K (u + t • u') (v + t • v') ≠ (⊥ : EReal) := by
    -- The translated-domain step lemma keeps the mixed point inside the finite patch.
    simpa using
      (helperForTheorem_35_6_scaledStep_finiteValues
        (C := C) (D := D) (K := K)
        hC_open hD_open hC_conv hD_conv hFinite hu hv
        (t := t) ht_pos ht_le hu' hv')
  have hAxisFinite :
      (K (u + t • u') v ≠ (⊤ : EReal) ∧ K (u + t • u') v ≠ (⊥ : EReal)) ∧
        (K u (v + t • v') ≠ (⊤ : EReal) ∧ K u (v + t • v') ≠ (⊥ : EReal)) := by
    -- The axis-step package supplies the two one-variable finite endpoints used below.
    simpa using
      (helperForTheorem_35_6_scaledAxisStep_finiteValues
        (C := C) (D := D) (K := K)
        hC_open hD_open hC_conv hD_conv hFinite hu hv
        (t := t) ht_pos ht_le hu' hv')
  have hBaseFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := hFinite u hu v hv
  have ht_ne : t ≠ 0 := ht_pos.ne'
  constructor
  · -- Convert the mixed quotient and the two addends to ordinary real quotients, then cancel the
    -- middle term `K (u + t • u') v`.
    have hMixedReal :
        ((K (u + t • u') (v + t • v') - K u v) / (t : EReal)).toReal =
          ((K (u + t • u') (v + t • v')).toReal - (K u v).toReal) / t := by
      rw [EReal.div_eq_inv_mul, EReal.toReal_mul]
      rw [EReal.toReal_sub hMixedFinite.1 hMixedFinite.2 hBaseFinite.1 hBaseFinite.2]
      have hInv : ((t : EReal)⁻¹).toReal = t⁻¹ := by
        rw [← EReal.coe_inv]
        simp
      rw [hInv]
      ring
    have hFirstAxisReal :
        ((K (u + t • u') v - K u v) / (t : EReal)).toReal =
          ((K (u + t • u') v).toReal - (K u v).toReal) / t := by
      rw [EReal.div_eq_inv_mul, EReal.toReal_mul]
      rw [EReal.toReal_sub hAxisFinite.1.1 hAxisFinite.1.2 hBaseFinite.1 hBaseFinite.2]
      have hInv : ((t : EReal)⁻¹).toReal = t⁻¹ := by
        rw [← EReal.coe_inv]
        simp
      rw [hInv]
      ring
    have hMovedSecondReal :
        ((K (u + t • u') (v + t • v') - K (u + t • u') v) / (t : EReal)).toReal =
          ((K (u + t • u') (v + t • v')).toReal - (K (u + t • u') v).toReal) / t := by
      rw [EReal.div_eq_inv_mul, EReal.toReal_mul]
      rw [EReal.toReal_sub hMixedFinite.1 hMixedFinite.2 hAxisFinite.1.1 hAxisFinite.1.2]
      have hInv : ((t : EReal)⁻¹).toReal = t⁻¹ := by
        rw [← EReal.coe_inv]
        simp
      rw [hInv]
      ring
    rw [saddleDirectionalDifferenceQuotientAt, hMixedReal, hFirstAxisReal, hMovedSecondReal]
    field_simp [ht_ne]
    ring
  · -- The symmetric decomposition cancels the middle term `K u (v + t • v')`.
    have hMixedReal :
        ((K (u + t • u') (v + t • v') - K u v) / (t : EReal)).toReal =
          ((K (u + t • u') (v + t • v')).toReal - (K u v).toReal) / t := by
      rw [EReal.div_eq_inv_mul, EReal.toReal_mul]
      rw [EReal.toReal_sub hMixedFinite.1 hMixedFinite.2 hBaseFinite.1 hBaseFinite.2]
      have hInv : ((t : EReal)⁻¹).toReal = t⁻¹ := by
        rw [← EReal.coe_inv]
        simp
      rw [hInv]
      ring
    have hSecondAxisReal :
        ((K u (v + t • v') - K u v) / (t : EReal)).toReal =
          ((K u (v + t • v')).toReal - (K u v).toReal) / t := by
      rw [EReal.div_eq_inv_mul, EReal.toReal_mul]
      rw [EReal.toReal_sub hAxisFinite.2.1 hAxisFinite.2.2 hBaseFinite.1 hBaseFinite.2]
      have hInv : ((t : EReal)⁻¹).toReal = t⁻¹ := by
        rw [← EReal.coe_inv]
        simp
      rw [hInv]
      ring
    have hMovedFirstReal :
        ((K (u + t • u') (v + t • v') - K u (v + t • v')) / (t : EReal)).toReal =
          ((K (u + t • u') (v + t • v')).toReal - (K u (v + t • v')).toReal) / t := by
      rw [EReal.div_eq_inv_mul, EReal.toReal_mul]
      rw [EReal.toReal_sub hMixedFinite.1 hMixedFinite.2 hAxisFinite.2.1 hAxisFinite.2.2]
      have hInv : ((t : EReal)⁻¹).toReal = t⁻¹ := by
        rw [← EReal.coe_inv]
        simp
      rw [hInv]
      ring
    rw [saddleDirectionalDifferenceQuotientAt, hMixedReal, hSecondAxisReal, hMovedFirstReal]
    field_simp [ht_ne]
    ring

/-- Helper for Theorem 35.6: for any fixed short second-variable step `η`, the translated
second-variable increment quotient converges back to the corresponding base-slice quotient along
every admissible positive null sequence in the first variable. -/
lemma helperForTheorem_35_6_fixedStepMovedSecondIncrement_tendsto_baseSecondQuotient
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (_hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    {τ : ℕ → ℝ}
    (hτpos : ∀ i, 0 < τ i) (hτle : ∀ i, τ i ≤ 1)
    (hτtendsto : Filter.Tendsto τ Filter.atTop (nhds (0 : ℝ)))
    {u' : Fin m → ℝ}
    (hu' : u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ)))
    {η : ℝ} (hηpos : 0 < η) (hηle : η ≤ 1)
    {v' : Fin n → ℝ}
    (hv' : v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ))) :
    Filter.Tendsto
      (fun i =>
        (((K (u + τ i • u') (v + η • v') - K (u + τ i • u') v) / (η : EReal)).toReal : ℝ))
      Filter.atTop
      (nhds (((K u (v + η • v') - K u v) / (η : EReal)).toReal : ℝ)) := by
  have hvEta : v + η • v' ∈ D := by
    have hvOne : v + v' ∈ D := hv'
    have hrewrite : v + η • v' = (1 - η) • v + η • (v + v') := by
      ext j
      simp [smul_add]
      ring
    -- Convexity keeps the fixed translated second-variable point inside `D`.
    rw [hrewrite]
    exact hD_conv hv hvOne (by linarith) hηpos.le (by linarith)
  have hLeftE :
      Filter.Tendsto (fun i => K (u + τ i • u') (v + η • v')) Filter.atTop
        (nhds (K u (v + η • v'))) :=
    helperForTheorem_35_6_movingSecondSlice_pointwiseTendstoOnD
      (C := C) (D := D) (K := K) hC_open hC_conv hK hFinite hu
      hτpos hτle hτtendsto hu' (v + η • v') hvEta
  have hRightE :
      Filter.Tendsto (fun i => K (u + τ i • u') v) Filter.atTop (nhds (K u v)) :=
    helperForTheorem_35_6_movingSecondSlice_pointwiseTendstoOnD
      (C := C) (D := D) (K := K) hC_open hC_conv hK hFinite hu
      hτpos hτle hτtendsto hu' v hv
  have hLeftFinite : K u (v + η • v') ≠ (⊤ : EReal) ∧ K u (v + η • v') ≠ (⊥ : EReal) :=
    hFinite u hu (v + η • v') hvEta
  have hRightFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := hFinite u hu v hv
  have hLeftR :
      Filter.Tendsto (fun i => (K (u + τ i • u') (v + η • v')).toReal) Filter.atTop
        (nhds ((K u (v + η • v')).toReal)) := by
    -- Convert the translated `EReal` values to real ones at the finite target.
    simpa using (EReal.tendsto_toReal hLeftFinite.1 hLeftFinite.2).comp hLeftE
  have hRightR :
      Filter.Tendsto (fun i => (K (u + τ i • u') v).toReal) Filter.atTop
        (nhds ((K u v).toReal)) := by
    -- The same conversion applies to the fixed base slice at `v`.
    simpa using (EReal.tendsto_toReal hRightFinite.1 hRightFinite.2).comp hRightE
  have hQuotReal :
      ∀ i,
        (((K (u + τ i • u') (v + η • v') - K (u + τ i • u') v) / (η : EReal)).toReal : ℝ) =
          ((K (u + τ i • u') (v + η • v')).toReal - (K (u + τ i • u') v).toReal) / η := by
    intro i
    have huu' : u + u' ∈ C := hu'
    have huStep : u + τ i • u' ∈ C := by
      have hrewrite : u + τ i • u' = (1 - τ i) • u + τ i • (u + u') := by
        ext j
        simp [smul_add]
        ring
      -- Convexity keeps each translated first-variable base point in `C`.
      rw [hrewrite]
      exact hC_conv hu huu' (by linarith [hτle i]) (hτpos i).le (by linarith)
    have hNumFinite :
        K (u + τ i • u') (v + η • v') ≠ (⊤ : EReal) ∧
          K (u + τ i • u') (v + η • v') ≠ (⊥ : EReal) :=
      hFinite (u + τ i • u') huStep (v + η • v') hvEta
    have hDenFinite :
        K (u + τ i • u') v ≠ (⊤ : EReal) ∧
          K (u + τ i • u') v ≠ (⊥ : EReal) :=
      hFinite (u + τ i • u') huStep v hv
    rw [EReal.div_eq_inv_mul, EReal.toReal_mul]
    rw [EReal.toReal_sub hNumFinite.1 hNumFinite.2 hDenFinite.1 hDenFinite.2]
    have hInv : ((η : EReal)⁻¹).toReal = η⁻¹ := by
      rw [← EReal.coe_inv]
      simp
    rw [hInv]
    ring
  have hTargetReal :
      (((K u (v + η • v') - K u v) / (η : EReal)).toReal : ℝ) =
        ((K u (v + η • v')).toReal - (K u v).toReal) / η := by
    rw [EReal.div_eq_inv_mul, EReal.toReal_mul]
    rw [EReal.toReal_sub hLeftFinite.1 hLeftFinite.2 hRightFinite.1 hRightFinite.2]
    have hInv : ((η : EReal)⁻¹).toReal = η⁻¹ := by
      rw [← EReal.coe_inv]
      simp
    rw [hInv]
    ring
  let movedReal : ℕ → ℝ := fun i =>
    ((K (u + τ i • u') (v + η • v')).toReal - (K (u + τ i • u') v).toReal) / η
  -- Rewrite both quotients in the real layer and use arithmetic continuity.
  have hEqSeq :
      Filter.EventuallyEq Filter.atTop
        (fun i =>
          (((K (u + τ i • u') (v + η • v') - K (u + τ i • u') v) / (η : EReal)).toReal : ℝ))
        movedReal :=
    Filter.Eventually.of_forall hQuotReal
  refine Filter.Tendsto.congr' hEqSeq.symm ?_
  simpa [movedReal, hTargetReal] using (hLeftR.sub hRightR).div_const η

/-- Helper for Theorem 35.6: for any fixed short first-variable step `η`, the translated
first-variable increment quotient converges back to the corresponding base-slice quotient along
every admissible positive null sequence in the second variable. -/
lemma helperForTheorem_35_6_fixedStepMovedFirstIncrement_tendsto_baseFirstQuotient
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (_hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    {τ : ℕ → ℝ}
    (hτpos : ∀ i, 0 < τ i) (hτle : ∀ i, τ i ≤ 1)
    (hτtendsto : Filter.Tendsto τ Filter.atTop (nhds (0 : ℝ)))
    {v' : Fin n → ℝ}
    (hv' : v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ)))
    {η : ℝ} (hηpos : 0 < η) (hηle : η ≤ 1)
    {u' : Fin m → ℝ}
    (hu' : u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ))) :
    Filter.Tendsto
      (fun i =>
        (((K (u + η • u') (v + τ i • v') - K u (v + τ i • v')) / (η : EReal)).toReal : ℝ))
      Filter.atTop
      (nhds (((K (u + η • u') v - K u v) / (η : EReal)).toReal : ℝ)) := by
  have huEta : u + η • u' ∈ C := by
    have huOne : u + u' ∈ C := hu'
    have hrewrite : u + η • u' = (1 - η) • u + η • (u + u') := by
      ext j
      simp [smul_add]
      ring
    -- Convexity keeps the fixed translated first-variable point inside `C`.
    rw [hrewrite]
    exact hC_conv hu huOne (by linarith) hηpos.le (by linarith)
  have hLeftE :
      Filter.Tendsto (fun i => K (u + η • u') (v + τ i • v')) Filter.atTop
        (nhds (K (u + η • u') v)) :=
    helperForTheorem_35_6_movingFirstSlice_pointwiseTendstoOnC
      (C := C) (D := D) (K := K) hD_open hD_conv hK hFinite hv
      hτpos hτle hτtendsto hv' (u + η • u') huEta
  have hRightE :
      Filter.Tendsto (fun i => K u (v + τ i • v')) Filter.atTop (nhds (K u v)) :=
    helperForTheorem_35_6_movingFirstSlice_pointwiseTendstoOnC
      (C := C) (D := D) (K := K) hD_open hD_conv hK hFinite hv
      hτpos hτle hτtendsto hv' u hu
  have hLeftFinite : K (u + η • u') v ≠ (⊤ : EReal) ∧ K (u + η • u') v ≠ (⊥ : EReal) :=
    hFinite (u + η • u') huEta v hv
  have hRightFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := hFinite u hu v hv
  have hLeftR :
      Filter.Tendsto (fun i => (K (u + η • u') (v + τ i • v')).toReal) Filter.atTop
        (nhds ((K (u + η • u') v).toReal)) := by
    -- Convert the translated `EReal` values to real ones at the finite target.
    simpa using (EReal.tendsto_toReal hLeftFinite.1 hLeftFinite.2).comp hLeftE
  have hRightR :
      Filter.Tendsto (fun i => (K u (v + τ i • v')).toReal) Filter.atTop
        (nhds ((K u v).toReal)) := by
    -- The same conversion applies to the fixed base slice at `u`.
    simpa using (EReal.tendsto_toReal hRightFinite.1 hRightFinite.2).comp hRightE
  have hQuotReal :
      ∀ i,
        (((K (u + η • u') (v + τ i • v') - K u (v + τ i • v')) / (η : EReal)).toReal : ℝ) =
          ((K (u + η • u') (v + τ i • v')).toReal - (K u (v + τ i • v')).toReal) / η := by
    intro i
    have hvv' : v + v' ∈ D := hv'
    have hvStep : v + τ i • v' ∈ D := by
      have hrewrite : v + τ i • v' = (1 - τ i) • v + τ i • (v + v') := by
        ext j
        simp [smul_add]
        ring
      -- Convexity keeps each translated second-variable base point in `D`.
      rw [hrewrite]
      exact hD_conv hv hvv' (by linarith [hτle i]) (hτpos i).le (by linarith)
    have hNumFinite :
        K (u + η • u') (v + τ i • v') ≠ (⊤ : EReal) ∧
          K (u + η • u') (v + τ i • v') ≠ (⊥ : EReal) :=
      hFinite (u + η • u') huEta (v + τ i • v') hvStep
    have hDenFinite :
        K u (v + τ i • v') ≠ (⊤ : EReal) ∧
          K u (v + τ i • v') ≠ (⊥ : EReal) :=
      hFinite u hu (v + τ i • v') hvStep
    rw [EReal.div_eq_inv_mul, EReal.toReal_mul]
    rw [EReal.toReal_sub hNumFinite.1 hNumFinite.2 hDenFinite.1 hDenFinite.2]
    have hInv : ((η : EReal)⁻¹).toReal = η⁻¹ := by
      rw [← EReal.coe_inv]
      simp
    rw [hInv]
    ring
  have hTargetReal :
      (((K (u + η • u') v - K u v) / (η : EReal)).toReal : ℝ) =
        ((K (u + η • u') v).toReal - (K u v).toReal) / η := by
    rw [EReal.div_eq_inv_mul, EReal.toReal_mul]
    rw [EReal.toReal_sub hLeftFinite.1 hLeftFinite.2 hRightFinite.1 hRightFinite.2]
    have hInv : ((η : EReal)⁻¹).toReal = η⁻¹ := by
      rw [← EReal.coe_inv]
      simp
    rw [hInv]
    ring
  let movedReal : ℕ → ℝ := fun i =>
    ((K (u + η • u') (v + τ i • v')).toReal - (K u (v + τ i • v')).toReal) / η
  -- Rewrite both quotients in the real layer and use arithmetic continuity.
  have hEqSeq :
      Filter.EventuallyEq Filter.atTop
        (fun i =>
          (((K (u + η • u') (v + τ i • v') - K u (v + τ i • v')) / (η : EReal)).toReal : ℝ))
        movedReal :=
    Filter.Eventually.of_forall hQuotReal
  refine Filter.Tendsto.congr' hEqSeq.symm ?_
  simpa [movedReal, hTargetReal] using (hLeftR.sub hRightR).div_const η


end Section35
end Chap07
