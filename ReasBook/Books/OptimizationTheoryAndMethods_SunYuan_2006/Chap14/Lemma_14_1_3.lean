/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.WeakDual
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_2

noncomputable section

open Bornology
open scoped ClarkeDirectionalDerivative ClarkeDifferential

section

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

local notation "DualSpace" => StrongDual ℝ X

/-
Domain sampling:
- primary domain: Clarke generalized gradients on real normed spaces
- sampled chapter owners:
  `LocallyLipschitzAt`, `clarkeDirectionalDeriv`, `clarkeDirectionalDerivReal`,
  `clarkeDifferential`
- sampled mathlib owners in the same duality/compactness domain:
  `StrongDual.toWeakDual`, `WeakDual.isCompact_closedBall`
- source-facing layer here: Lemma 14.1.3 properties of `clarkeDifferential`
- core/canonical owner reused here: `clarkeDifferential`
- bridge/view owner reused here: `clarkeDirectionalDerivReal`
- primitive data: a local Lipschitz hypothesis at `x`
- derived API: the basic nonempty/convex/compact/maximality properties of the Clarke differential
- refinement target: source-facing derived lemmas over the canonical owner `clarkeDifferential`,
  with no Banach-space hypothesis in the ambient file context
-/

/-- Helper for Chapter14 Lemma 14.1.3: under a local Lipschitz hypothesis, membership in the
Clarke differential can be read against the real-valued Clarke directional derivative. -/
lemma mem_clarkeDifferential_real_iff_of_locallyLipschitzAt
    (f : X → ℝ) (x : X) (h_local : LocallyLipschitzAt f x) (ξ : DualSpace) :
    ξ ∈ (∂ᶜ f) x ↔ ∀ d : X, ξ d ≤ clarkeDirectionalDerivReal f x d := by
  constructor
  · intro hξ d
    -- Transport the defining `EReal` inequality through the local-Lipschitz finiteness bridge.
    have hξd :
        (((ξ d : ℝ) : EReal) ≤ ((clarkeDirectionalDerivReal f x d : ℝ) : EReal)) := by
      simpa [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d h_local] using
        ((mem_clarkeDifferential_iff f x ξ).1 hξ d)
    exact_mod_cast hξd
  · intro hξ
    -- Repackage the real support inequalities back into the canonical `EReal` definition.
    rw [mem_clarkeDifferential_iff]
    intro d
    have hξd :
        (((ξ d : ℝ) : EReal) ≤ ((clarkeDirectionalDerivReal f x d : ℝ) : EReal)) := by
      exact_mod_cast hξ d
    simpa [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d h_local] using hξd

/-- Helper for Chapter14 Lemma 14.1.3: the real-valued Clarke directional derivative vanishes at
the zero direction. -/
lemma clarkeDirectionalDerivReal_zero_of_locallyLipschitzAt
    (f : X → ℝ) (x : X) (h_local : LocallyLipschitzAt f x) :
    clarkeDirectionalDerivReal f x (0 : X) = 0 := by
  -- This is the `λ = 0` branch of positive homogeneity from Lemma 14.1.1.
  have hzero :
      fᵒ(x; (0 : ℝ) • (0 : X)) = (0 : ℝ) * fᵒ(x; (0 : X)) :=
    clarkeDirectionalDerivative_posHomogeneous (f := f) (x := x) h_local (0 : X) 0
      (by norm_num)
  have hzero' : (((clarkeDirectionalDerivReal f x (0 : X) : ℝ) : EReal) = (0 : EReal)) := by
    simpa using hzero
  exact_mod_cast hzero'

/-- Helper for Chapter14 Lemma 14.1.3: the real-valued Clarke directional derivative is
subadditive under the local Lipschitz hypothesis. -/
lemma clarkeDirectionalDerivReal_subadditive
    (f : X → ℝ) (x : X) (h_local : LocallyLipschitzAt f x) (d₁ d₂ : X) :
    clarkeDirectionalDerivReal f x (d₁ + d₂) ≤
      clarkeDirectionalDerivReal f x d₁ + clarkeDirectionalDerivReal f x d₂ := by
  -- Move the `EReal` subadditivity result from Lemma 14.1.1 to the finite real-valued surface.
  have hsub :
      fᵒ(x; d₁ + d₂) ≤ fᵒ(x; d₁) + fᵒ(x; d₂) :=
    clarkeDirectionalDerivative_subadditive (f := f) (x := x) h_local d₁ d₂
  have hsub' :
      (((clarkeDirectionalDerivReal f x (d₁ + d₂) : ℝ) : EReal) ≤
        ((clarkeDirectionalDerivReal f x d₁ : ℝ) : EReal) +
          ((clarkeDirectionalDerivReal f x d₂ : ℝ) : EReal)) := by
    simpa
      [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x (d₁ + d₂) h_local,
        coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d₁ h_local,
        coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d₂ h_local]
      using hsub
  exact_mod_cast hsub'

/-- Helper for Chapter14 Lemma 14.1.3: on the span of a fixed direction `d`, the linear functional
`a • d ↦ a * clarkeDirectionalDerivReal f x d` is dominated by the Clarke support function. -/
lemma smul_clarkeDirectionalDerivReal_le_of_locallyLipschitzAt
    (f : X → ℝ) (x d : X) (h_local : LocallyLipschitzAt f x) (a : ℝ) :
    a * clarkeDirectionalDerivReal f x d ≤ clarkeDirectionalDerivReal f x (a • d) := by
  by_cases ha : 0 ≤ a
  · -- For nonnegative scalars this is exactly positive homogeneity.
    have hhom :
        fᵒ(x; a • d) = a * fᵒ(x; d) :=
      clarkeDirectionalDerivative_posHomogeneous (f := f) (x := x) h_local d a ha
    have hhom' :
        ((clarkeDirectionalDerivReal f x (a • d) : ℝ) : EReal) =
          ((a * clarkeDirectionalDerivReal f x d : ℝ) : EReal) := by
      simpa
        [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x (a • d) h_local,
          coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d h_local]
        using hhom
    exact le_of_eq (by exact_mod_cast hhom'.symm)
  · have ha_neg : 0 ≤ -a := by linarith
    have hsub :
        clarkeDirectionalDerivReal f x (a • d + (-a) • d) ≤
          clarkeDirectionalDerivReal f x (a • d) + clarkeDirectionalDerivReal f x ((-a) • d) :=
      clarkeDirectionalDerivReal_subadditive (f := f) (x := x) h_local (a • d) ((-a) • d)
    have hneg :
        clarkeDirectionalDerivReal f x ((-a) • d) = (-a) * clarkeDirectionalDerivReal f x d := by
      -- The positive-homogeneous branch applies to `-a > 0`.
      have hhom :
          fᵒ(x; (-a) • d) = (-a) * fᵒ(x; d) :=
        clarkeDirectionalDerivative_posHomogeneous (f := f) (x := x) h_local d (-a) ha_neg
      have hhom' :
          ((clarkeDirectionalDerivReal f x ((-a) • d) : ℝ) : EReal) =
            (((-a) * clarkeDirectionalDerivReal f x d : ℝ) : EReal) := by
        simpa
          [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x ((-a) • d) h_local,
            coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d h_local]
          using hhom
      exact_mod_cast hhom'
    have hzero :
        clarkeDirectionalDerivReal f x (0 : X) = 0 :=
      clarkeDirectionalDerivReal_zero_of_locallyLipschitzAt (f := f) (x := x) h_local
    have hnonneg :
        0 ≤ clarkeDirectionalDerivReal f x (a • d) + (-a) * clarkeDirectionalDerivReal f x d := by
      calc
        0 = clarkeDirectionalDerivReal f x (a • d + (-a) • d) := by
          simpa [hzero, add_smul]
        _ ≤ clarkeDirectionalDerivReal f x (a • d) + clarkeDirectionalDerivReal f x ((-a) • d) :=
          hsub
        _ = clarkeDirectionalDerivReal f x (a • d) + (-a) * clarkeDirectionalDerivReal f x d := by
          rw [hneg]
    linarith

/-- Helper for Chapter14 Lemma 14.1.3: Hahn-Banach produces a generalized gradient that attains
the real-valued Clarke directional derivative in a prescribed direction. -/
lemma exists_mem_clarkeDifferential_eval_eq_clarkeDirectionalDerivReal_of_locallyLipschitzAt
    (f : X → ℝ) (x d : X) (h_local : LocallyLipschitzAt f x) :
    ∃ ξ : DualSpace, ξ ∈ (∂ᶜ f) x ∧ ξ d = clarkeDirectionalDerivReal f x d := by
  let N : X → ℝ := fun y ↦ clarkeDirectionalDerivReal f x y
  have hN_zero : N 0 = 0 :=
    clarkeDirectionalDerivReal_zero_of_locallyLipschitzAt (f := f) (x := x) h_local
  have hN_hom : ∀ c : ℝ, 0 < c → ∀ y, N (c • y) = c * N y := by
    intro c hc y
    -- Positive homogeneity is the source input for Hahn-Banach.
    have hhom :
        fᵒ(x; c • y) = c * fᵒ(x; y) :=
      clarkeDirectionalDerivative_posHomogeneous (f := f) (x := x) h_local y c hc.le
    have hhom' : (((N (c • y) : ℝ) : EReal) = ((c * N y : ℝ) : EReal)) := by
      simpa
        [N, coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x (c • y) h_local,
          coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x y h_local]
        using hhom
    exact_mod_cast hhom'
  have hN_add : ∀ y z, N (y + z) ≤ N y + N z := by
    intro y z
    exact clarkeDirectionalDerivReal_subadditive (f := f) (x := x) h_local y z
  have hsingleton : ∀ c : ℝ, c • d = 0 → c • N d = 0 := by
    intro c hc
    rcases smul_eq_zero.mp hc with hc0 | hd0
    · simp [hc0]
    · have hNd0 : N d = 0 := by
        subst hd0
        simpa [N] using hN_zero
      simp [hNd0]
  let pmap : X →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' d (N d) hsingleton
  have hpmap_le : ∀ y : pmap.domain, pmap y ≤ N y := by
    intro y
    rcases y with ⟨y, hy⟩
    change pmap ⟨y, hy⟩ ≤ N y
    rcases Submodule.mem_span_singleton.mp hy with ⟨a, rfl⟩
    have ha_mem : a • d ∈ Submodule.span ℝ ({d} : Set X) :=
      Submodule.mem_span_singleton.2 ⟨a, rfl⟩
    -- On the one-dimensional domain, the source supporting inequality is exactly the scalar case.
    have hpmap_eval : pmap ⟨a • d, ha_mem⟩ = ((RingHom.id ℝ) a) • N d := by
      change (LinearPMap.mkSpanSingleton' d (N d) hsingleton) ⟨a • d, ha_mem⟩ =
        ((RingHom.id ℝ) a) • N d
      exact LinearPMap.mkSpanSingleton'_apply d (N d) hsingleton a ha_mem
    have hscalar : ((RingHom.id ℝ) a) • N d ≤ N (a • d) := by
      simpa [smul_eq_mul] using
        smul_clarkeDirectionalDerivReal_le_of_locallyLipschitzAt (f := f) (x := x) (d := d)
          h_local a
    exact hpmap_eval ▸ hscalar
  obtain ⟨g, hg_eq, hg_le⟩ := exists_extension_of_le_sublinear pmap N hN_hom hN_add hpmap_le
  rcases locallyLipschitzAt_iff.mp h_local with ⟨ε, hε, K, hK⟩
  have hg_norm : ∀ y, ‖g y‖ ≤ (K : ℝ) * ‖y‖ := by
    intro y
    have hgy_upper : g y ≤ N y := hg_le y
    have hgy_lower : -((K : ℝ) * ‖y‖) ≤ g y := by
      -- Apply the domination inequality to `-y` and combine it with the Lipschitz bound.
      have hneg : -g y ≤ N (-y) := by
        simpa [N] using hg_le (-y)
      have hneg_bound :
          N (-y) ≤ (K : ℝ) * ‖y‖ := by
        have habs :=
          clarkeDirectionalDerivative_abs_le (f := f) (x := x) (d := -y) K ⟨ε, hε, hK⟩
        simpa [N] using (abs_le.mp habs).2
      linarith [hneg, hneg_bound]
    have hgy_upper' : g y ≤ (K : ℝ) * ‖y‖ := by
      have habs :=
        clarkeDirectionalDerivative_abs_le (f := f) (x := x) (d := y) K ⟨ε, hε, hK⟩
      have hbound : N y ≤ (K : ℝ) * ‖y‖ := by
        simpa [N] using (abs_le.mp habs).2
      exact le_trans hgy_upper hbound
    simpa [Real.norm_eq_abs] using abs_le.mpr ⟨hgy_lower, hgy_upper'⟩
  let ξ : DualSpace := g.mkContinuous (K : ℝ) hg_norm
  have hξ_mem : ξ ∈ (∂ᶜ f) x := by
    -- The continuous Hahn-Banach extension satisfies the Clarke support inequalities everywhere.
    refine (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt
      (f := f) (x := x) h_local ξ).2 ?_
    intro y
    simpa [ξ, N] using hg_le y
  have hξ_eval : ξ d = N d := by
    have hd_mem : d ∈ pmap.domain := by
      simpa [pmap] using (Submodule.mem_span_singleton_self d : d ∈ Submodule.span ℝ ({d} : Set X))
    have hd_eq : g d = pmap ⟨d, hd_mem⟩ := hg_eq ⟨d, hd_mem⟩
    have hpmap_d : pmap ⟨d, hd_mem⟩ = N d := by
      simpa [pmap, N] using LinearPMap.mkSpanSingleton'_apply_self d (N d) hsingleton hd_mem
    simpa [ξ] using hd_eq.trans hpmap_d
  exact ⟨ξ, hξ_mem, hξ_eval⟩

/-- Helper for Chapter14 Lemma 14.1.3: a generalized gradient belonging to the Clarke
differential is bounded in norm by the local closed-ball Lipschitz constant. -/
lemma norm_le_of_mem_clarkeDifferential_of_closedBallLipschitz_aux
    (f : X → ℝ) (x : X) (K : NNReal) {ξ : DualSpace}
    (hK : ∃ ε : ℝ, (0 : ℝ) < ε ∧ LipschitzOnWith K f (Metric.closedBall x ε))
    (hξ : ξ ∈ (∂ᶜ f) x) :
    ‖ξ‖ ≤ (K : ℝ) := by
  let N : X → ℝ := fun d ↦ clarkeDirectionalDerivReal f x d
  have h_local : LocallyLipschitzAt f x := locallyLipschitzAt_of_closedBall hK
  have hξ_real :
      ∀ d : X, ξ d ≤ N d :=
    (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt (f := f) (x := x) h_local ξ).1 hξ
  -- Bound each evaluation by comparing both `d` and `-d` with the same Lipschitz witness.
  refine ContinuousLinearMap.opNorm_le_bound _ K.2 ?_
  intro d
  have hupper : ξ d ≤ (K : ℝ) * ‖d‖ := by
    have habs := clarkeDirectionalDerivative_abs_le (f := f) (x := x) (d := d) K hK
    exact le_trans (hξ_real d) (by simpa [N] using (abs_le.mp habs).2)
  have hlower : -((K : ℝ) * ‖d‖) ≤ ξ d := by
    have hneg : -ξ d ≤ N (-d) := by
      simpa [N] using hξ_real (-d)
    have habs := clarkeDirectionalDerivative_abs_le (f := f) (x := x) (d := -d) K hK
    have hneg_bound : N (-d) ≤ (K : ℝ) * ‖d‖ := by
      simpa [N] using (abs_le.mp habs).2
    linarith
  simpa [Real.norm_eq_abs] using abs_le.mpr ⟨hlower, hupper⟩

/-- Helper for Chapter14 Lemma 14.1.3: the weak-* image of the Clarke differential is exactly the
intersection of the evaluation halfspaces defined by the real-valued Clarke derivative. -/
lemma toWeakDual_mem_image_clarkeDifferential_iff_of_locallyLipschitzAt
    (f : X → ℝ) (x : X) (h_local : LocallyLipschitzAt f x) (η : WeakDual ℝ X) :
    η ∈ StrongDual.toWeakDual '' (∂ᶜ f) x ↔
      ∀ d : X, η d ≤ clarkeDirectionalDerivReal f x d := by
  constructor
  · rintro ⟨ξ, hξ, rfl⟩ d
    -- Forgetting the norm topology does not change the evaluation inequalities.
    simpa using
      (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt (f := f) (x := x) h_local ξ).1 hξ d
  · intro hη
    let ξ : DualSpace := WeakDual.toStrongDual η
    have hξ_mem : ξ ∈ (∂ᶜ f) x := by
      -- Convert the weak-dual point back to the strong dual using the defining inequalities.
      refine (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt
        (f := f) (x := x) h_local ξ).2 ?_
      intro d
      simpa [ξ] using hη d
    exact ⟨ξ, hξ_mem, rfl⟩

/-- Chapter14 Lemma 14.1.3 (1): if `f` is Lipschitz near `x`, then the Clarke differential
`(∂ᶜ f) x = ∂ᶜ f(x)` is nonempty. -/
theorem clarkeDifferential_nonempty_of_locallyLipschitzAt
    (f : X → ℝ) (x : X) (h_local : LocallyLipschitzAt f x) :
    ((∂ᶜ f) x).Nonempty := by
  -- Use the Hahn-Banach attaining functional in the zero direction to witness nonemptiness.
  rcases exists_mem_clarkeDifferential_eval_eq_clarkeDirectionalDerivReal_of_locallyLipschitzAt
      (f := f) (x := x) (d := 0) h_local with ⟨ξ, hξ, _⟩
  exact ⟨ξ, hξ⟩

/-- Chapter14 Lemma 14.1.3 (2): if `f` is Lipschitz near `x`, then the Clarke differential
`(∂ᶜ f) x = ∂ᶜ f(x)` is convex. -/
theorem convex_clarkeDifferential_of_locallyLipschitzAt
    (f : X → ℝ) (x : X) (h_local : LocallyLipschitzAt f x) :
    Convex ℝ ((∂ᶜ f) x) := by
  intro ξ hξ η hη a b ha hb hab
  refine (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt
    (f := f) (x := x) h_local (a • ξ + b • η)).2 ?_
  intro d
  -- Convexity is pointwise: each evaluation remains below the same support bound.
  have hξd :
      ξ d ≤ clarkeDirectionalDerivReal f x d :=
    (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt
      (f := f) (x := x) h_local ξ).1 hξ d
  have hηd :
      η d ≤ clarkeDirectionalDerivReal f x d :=
    (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt
      (f := f) (x := x) h_local η).1 hη d
  calc
    (a • ξ + b • η) d = a * ξ d + b * η d := by simp [smul_eq_mul]
    _ ≤ a * clarkeDirectionalDerivReal f x d + b * clarkeDirectionalDerivReal f x d := by
      gcongr
    _ = (a + b) * clarkeDirectionalDerivReal f x d := by ring
    _ = clarkeDirectionalDerivReal f x d := by simp [hab]

/-- Chapter14 Lemma 14.1.3 (3): if `f` is Lipschitz near `x`, then
`(∂ᶜ f) x = ∂ᶜ f(x)` is weak-* compact, expressed as compactness of its image in
`WeakDual ℝ X`. -/
theorem isCompact_toWeakDual_image_clarkeDifferential_of_locallyLipschitzAt
    (f : X → ℝ) (x : X) (h_local : LocallyLipschitzAt f x) :
    IsCompact (StrongDual.toWeakDual '' (∂ᶜ f) x) := by
  let S : Set (WeakDual ℝ X) := StrongDual.toWeakDual '' (∂ᶜ f) x
  rcases locallyLipschitzAt_iff.mp h_local with ⟨ε, hε, K, hK⟩
  have hclosed : IsClosed S := by
    -- Identify the weak-* image with an intersection of evaluation halfspaces.
    have hrepr :
        S = ⋂ d : X, {η : WeakDual ℝ X | η d ≤ clarkeDirectionalDerivReal f x d} := by
      ext η
      simp [S, toWeakDual_mem_image_clarkeDifferential_iff_of_locallyLipschitzAt
        (f := f) (x := x) h_local η]
    rw [hrepr]
    exact isClosed_iInter fun d => isClosed_Iic.preimage (WeakDual.eval_continuous d)
  have hbounded : IsBounded S := by
    -- The norm bound from part (4) transfers boundedness to the weak-* image.
    rw [← WeakDual.isBounded_toWeakDual_preimage_iff_isBounded]
    simpa [S, Set.preimage_image_eq, StrongDual.toWeakDual.injective] using
      (isBounded_iff_forall_norm_le.2 ⟨(K : ℝ), fun ξ hξ ↦
        norm_le_of_mem_clarkeDifferential_of_closedBallLipschitz_aux
          (f := f) (x := x) (K := K) ⟨ε, hε, hK⟩ hξ⟩)
  exact WeakDual.isCompact_of_bounded_of_closed hbounded hclosed

/-- Chapter14 Lemma 14.1.3 (4): if `f` is `K`-Lipschitz on some closed ball centered at `x`,
then every generalized gradient `ξ ∈ ∂ᶜ f(x)` satisfies `‖ξ‖ ≤ K`. -/
theorem norm_le_of_mem_clarkeDifferential_of_closedBallLipschitz
    (f : X → ℝ) (x : X) (K : NNReal) {ξ : DualSpace}
    (hK : ∃ ε : ℝ, (0 : ℝ) < ε ∧ LipschitzOnWith K f (Metric.closedBall x ε))
    (hξ : ξ ∈ (∂ᶜ f) x) :
    ‖ξ‖ ≤ (K : ℝ) := by
  -- This is the norm-control helper proved before compactness.
  exact norm_le_of_mem_clarkeDifferential_of_closedBallLipschitz_aux
    (f := f) (x := x) (K := K) hK hξ

/-- Chapter14 Lemma 14.1.3 (5): if `f` is Lipschitz near `x`, then for every direction `d` the
finite real-valued Clarke directional derivative is the maximum of the pairing `ξ d`
over `ξ ∈ ∂ᶜ f(x)`, formalized as an `IsGreatest` statement for the image set `(14.1.20)`. -/
theorem clarkeDirectionalDeriv_isGreatest_image_clarkeDifferential_of_locallyLipschitzAt
    (f : X → ℝ) (x d : X) (h_local : LocallyLipschitzAt f x) :
    IsGreatest
      ((fun ξ : DualSpace ↦ ξ d) '' (∂ᶜ f) x)
      (clarkeDirectionalDerivReal f x d) := by
  rcases exists_mem_clarkeDifferential_eval_eq_clarkeDirectionalDerivReal_of_locallyLipschitzAt
      (f := f) (x := x) (d := d) h_local with ⟨ξ, hξ, hξd⟩
  refine ⟨⟨ξ, hξ, hξd⟩, ?_⟩
  intro y hy
  rcases hy with ⟨η, hη, rfl⟩
  -- The attaining functional gives membership, and every other generalized gradient lies below it.
  exact
    (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt
      (f := f) (x := x) h_local η).1 hη d

#print axioms clarkeDirectionalDeriv
#print axioms clarkeDifferential

end
