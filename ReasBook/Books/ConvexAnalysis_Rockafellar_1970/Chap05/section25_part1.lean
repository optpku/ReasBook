/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section10_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part4

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

/-- The first-order error quotient for an `EReal`-valued function along finite-valued points. -/
noncomputable def erealGradientErrorQuotient {n : Nat} (f : (Fin n → Real) → EReal)
    (x g : Fin n → Real) : (Fin n → Real) → Real :=
  fun z => (((f z - f x).toReal) - g ⬝ᵥ (z - x)) / ‖z - x‖

/-- An `EReal`-valued function has gradient `g` at `x` when `f x` is finite and the normalized
first-order error tends to `0` as `z → x` through finite-valued points of the punctured
neighborhood of `x`. -/
noncomputable def HasERealGradientAt {n : Nat} (f : (Fin n → Real) → EReal)
    (x g : Fin n → Real) : Prop :=
  f x ≠ ⊤ ∧ f x ≠ ⊥ ∧
    Filter.Tendsto (erealGradientErrorQuotient f x g)
      (nhdsWithin x
        ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f))
      (nhds 0)

/-- Definition 25.1: an `EReal`-valued function on `ℝ^n` is differentiable at `x` when there
exists a vector `g` such that `f x` is finite and
`(f z - f x - g ⬝ᵥ (z - x)) / ‖z - x‖ → 0` as `z → x` through punctured nearby points where `f`
is finite. In addition, nearby punctured points are eventually finite-valued, so the first-order
expansion can be evaluated along every sufficiently short ray. -/
noncomputable def ERealDifferentiableAt {n : Nat} (f : (Fin n → Real) → EReal)
    (x : Fin n → Real) : Prop :=
  ∃ g : Fin n → Real,
    HasERealGradientAt f x g ∧
      (∀ᶠ z in nhdsWithin x ({z | z ≠ x}),
        z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f ∧ f z ≠ ⊥)

/-- A chosen gradient witness for an `EReal`-differentiable function at `x`. -/
noncomputable def erealGradientAt {n : Nat} {f : (Fin n → Real) → EReal}
    {x : Fin n → Real} (hf : ERealDifferentiableAt f x) : Fin n → Real :=
  Classical.choose hf

/-- The chosen differentiability witness satisfies the first-order expansion predicate. -/
theorem ERealDifferentiableAt.hasERealGradientAt {n : Nat} {f : (Fin n → Real) → EReal}
    {x : Fin n → Real} (hf : ERealDifferentiableAt f x) :
    HasERealGradientAt f x (erealGradientAt hf) :=
  (Classical.choose_spec hf).1

/-- Differentiability at `x` forces `f x` to be finite. -/
theorem ERealDifferentiableAt.finiteAt {n : Nat} {f : (Fin n → Real) → EReal}
    {x : Fin n → Real} (hf : ERealDifferentiableAt f x) :
    f x ≠ ⊤ ∧ f x ≠ ⊥ :=
  ⟨(ERealDifferentiableAt.hasERealGradientAt hf).1,
    (ERealDifferentiableAt.hasERealGradientAt hf).2.1⟩

/-- Differentiability at `x` includes eventual finite-valued control on the punctured
neighborhood of `x`. -/
theorem ERealDifferentiableAt.eventually_finiteValuedWithin_punctured
    {n : Nat} {f : (Fin n → Real) → EReal} {x : Fin n → Real}
    (hf : ERealDifferentiableAt f x) :
    ∀ᶠ z in nhdsWithin x ({z | z ≠ x}),
      z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f ∧ f z ≠ ⊥ :=
  (Classical.choose_spec hf).2

-- Proof sketch: compare the two asymptotic expansions and test the resulting linear form on rays
-- through `x` to force equality of the candidate gradients.
/-- Helper for Theorem 25.1: a gradient witness together with eventual finite-valued control
identifies every nonzero directional difference quotient limit. -/
lemma helperForTheorem_25_1_directionalDifferenceQuotient_tendsto_dotGradient_of_hasERealGradientAt
    {n : Nat} {f : (Fin n → Real) → EReal} {x g y : Fin n → Real}
    (hg : HasERealGradientAt f x g)
    (hfinite :
      ∀ᶠ z in nhdsWithin x ({z | z ≠ x}),
        z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f ∧ f z ≠ ⊥)
    (hy : y ≠ 0) :
    Filter.Tendsto (directionalDifferenceQuotientAt f x y)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (((g ⬝ᵥ y : Real) : EReal))) := by
  have hx : f x ≠ ⊤ ∧ f x ≠ ⊥ := ⟨hg.1, hg.2.1⟩
  -- The positive ray approaches `x` through punctured points.
  have hrayToPunctured :
      Filter.Tendsto (fun t : Real => x + t • y)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhdsWithin x {z | z ≠ x}) := by
    have hcont : ContinuousAt (fun t : Real => x + t • y) (0 : Real) := by
      fun_prop
    have hwithin :
        ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0), x + t • y ∈ ({z | z ≠ x} : Set _) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      intro hEq
      have hsmul : t • y = 0 := by
        exact add_left_cancel (by simpa using hEq : x + t • y = x + 0)
      rcases smul_eq_zero.mp hsmul with ht0 | hy0
      · exact (ne_of_gt ht) ht0
      · exact hy hy0
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ hwithin
    simpa [zero_smul] using (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  -- Pull the finite-valued punctured-neighborhood control back along the ray.
  have hfiniteRay :
      ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
        x + t • y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f ∧
          f (x + t • y) ≠ ⊥ := by
    exact hrayToPunctured.eventually hfinite
  have hray :
      ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
        x + t • y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    exact hfiniteRay.mono fun _ ht => ht.1
  have hrayInto :
      Filter.Tendsto (fun t : Real => x + t • y)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhdsWithin x
          ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
    have hcont : ContinuousAt (fun t : Real => x + t • y) (0 : Real) := by
      fun_prop
    have hwithin :
        ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
          x + t • y ∈
            ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
      filter_upwards [self_mem_nhdsWithin, hray] with t ht hmem
      refine ⟨?_, hmem⟩
      intro hEq
      have hsmul : t • y = 0 := by
        exact add_left_cancel (by simpa using hEq : x + t • y = x + 0)
      rcases smul_eq_zero.mp hsmul with ht0 | hy0
      · exact (ne_of_gt ht) ht0
      · exact hy hy0
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ hwithin
    simpa [zero_smul] using (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  -- Compose the gradient-error limit with the ray parametrization.
  have herrorRay :
      Filter.Tendsto (fun t : Real => erealGradientErrorQuotient f x g (x + t • y))
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds 0) :=
    hg.2.2.comp hrayInto
  -- Rewrite the real quotient as an affine perturbation of the error term.
  have hrealEq :
      ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
        ((f (x + t • y)).toReal - (f x).toReal) / t =
          ‖y‖ * erealGradientErrorQuotient f x g (x + t • y) + g ⬝ᵥ y := by
    filter_upwards [self_mem_nhdsWithin, hfiniteRay] with t ht htFinite
    have htne : t ≠ 0 := ne_of_gt ht
    have hyNorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    have htop : f (x + t • y) ≠ ⊤ :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) htFinite.1
    have hsub :
        x + t • y - x = t • y := by
      simp [sub_eq_add_neg, add_assoc]
    have hdot :
        g ⬝ᵥ (t • y) = t * (g ⬝ᵥ y) := by
      simpa [smul_eq_mul] using (dotProduct_smul t g y)
    have hnorm :
        ‖t • y‖ = t * ‖y‖ := by
      simpa [Real.norm_of_nonneg (le_of_lt ht)] using norm_smul t y
    have htoRealSub :
        (f (x + t • y) - f x).toReal = (f (x + t • y)).toReal - (f x).toReal := by
      simpa using EReal.toReal_sub htop htFinite.2 hx.1 hx.2
    rw [erealGradientErrorQuotient, hsub, hdot, hnorm, htoRealSub]
    field_simp [htne, hyNorm]
    ring
  have hrealTendsto :
      Filter.Tendsto (fun t : Real => ((f (x + t • y)).toReal - (f x).toReal) / t)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds (g ⬝ᵥ y)) := by
    have hAffine :
        Filter.Tendsto
          (fun t : Real => ‖y‖ * erealGradientErrorQuotient f x g (x + t • y) + g ⬝ᵥ y)
          (nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds (g ⬝ᵥ y)) := by
      have hcont : Continuous (fun r : Real => ‖y‖ * r + g ⬝ᵥ y) := by
        fun_prop
      simpa using hcont.continuousAt.tendsto.comp herrorRay
    refine Filter.Tendsto.congr' ?_ hAffine
    filter_upwards [hrealEq] with t htEq
    exact htEq.symm
  -- Coerce the real quotient to match the textbook `EReal` directional quotient.
  have hcoereal :
      Filter.Tendsto
        (fun t : Real => ((((f (x + t • y)).toReal - (f x).toReal) / t : Real) : EReal))
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds (((g ⬝ᵥ y : Real) : EReal))) :=
    (EReal.tendsto_coe).2 hrealTendsto
  have hquotEq :
      ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
        directionalDifferenceQuotientAt f x y t =
          ((((f (x + t • y)).toReal - (f x).toReal) / t : Real) : EReal) := by
    filter_upwards [self_mem_nhdsWithin, hfiniteRay] with t ht htFinite
    have htop : f (x + t • y) ≠ ⊤ :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) htFinite.1
    simp [directionalDifferenceQuotientAt, EReal.coe_div, EReal.coe_sub,
      EReal.coe_toReal htop htFinite.2, EReal.coe_toReal hx.1 hx.2]
  exact Filter.Tendsto.congr' (by
    filter_upwards [hquotEq] with t htEq
    exact htEq.symm) hcoereal

/-- Two gradients satisfying the first-order expansion at the same point coincide once nearby
punctured points are eventually finite-valued. -/
theorem erealGradient_unique {n : Nat} {f : (Fin n → Real) → EReal} {x g₁ g₂ : Fin n → Real}
    (hfinite :
      ∀ᶠ z in nhdsWithin x ({z | z ≠ x}),
        z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f ∧ f z ≠ ⊥)
    (hg₁ : HasERealGradientAt f x g₁) (hg₂ : HasERealGradientAt f x g₂) : g₁ = g₂ := by
  -- Compare the directional quotient limits produced by the two candidate gradients.
  ext j
  have hbasis_ne : (Pi.single j (1 : Real) : Fin n → Real) ≠ 0 := by
    intro hzero
    have : (Pi.single j (1 : Real) : Fin n → Real) j = (0 : Fin n → Real) j := by
      simpa using congrArg (fun v : Fin n → Real => v j) hzero
    simpa using this
  have hlimit₁ :
      Filter.Tendsto (directionalDifferenceQuotientAt f x (Pi.single j (1 : Real)))
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds (((g₁ ⬝ᵥ Pi.single j (1 : Real) : Real) : EReal))) :=
    helperForTheorem_25_1_directionalDifferenceQuotient_tendsto_dotGradient_of_hasERealGradientAt
      (g := g₁) (y := Pi.single j (1 : Real)) hg₁ hfinite hbasis_ne
  have hlimit₂ :
      Filter.Tendsto (directionalDifferenceQuotientAt f x (Pi.single j (1 : Real)))
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds (((g₂ ⬝ᵥ Pi.single j (1 : Real) : Real) : EReal))) :=
    helperForTheorem_25_1_directionalDifferenceQuotient_tendsto_dotGradient_of_hasERealGradientAt
      (g := g₂) (y := Pi.single j (1 : Real)) hg₂ hfinite hbasis_ne
  have hdotEq :
      (((g₁ ⬝ᵥ Pi.single j (1 : Real) : Real) : EReal)) =
        (((g₂ ⬝ᵥ Pi.single j (1 : Real) : Real) : EReal)) := by
    haveI : Filter.NeBot (nhdsWithin (0 : Real) (Set.Ioi 0)) :=
      nhdsWithin_Ioi_neBot (a := (0 : Real)) (b := (0 : Real)) le_rfl
    exact tendsto_nhds_unique hlimit₁ hlimit₂
  have hdotEqReal :
      g₁ ⬝ᵥ Pi.single j (1 : Real) = g₂ ⬝ᵥ Pi.single j (1 : Real) :=
    (EReal.coe_eq_coe_iff).1 hdotEq
  simpa [dotProduct_single_one] using hdotEqReal

/-- Helper for Theorem 25.1: a positive step in a nonzero direction never returns to the base
point. -/
lemma helperForTheorem_25_1_nonzero_ray_ne {n : Nat} {x y : Fin n → Real}
    (hy : y ≠ 0) {t : Real} (ht : 0 < t) :
    x + t • y ≠ x := by
  intro hEq
  -- Cancel the common base point to isolate the scaled direction.
  have hsmul : t • y = 0 := by
    exact add_left_cancel (by simpa using hEq : x + t • y = x + 0)
  -- A positive scalar cannot kill a nonzero vector over `ℝ`.
  rcases smul_eq_zero.mp hsmul with ht0 | hy0
  · exact (ne_of_gt ht) ht0
  · exact hy hy0

/-- Helper for Theorem 25.1: the positive ray `t ↦ x + t • y` tends to `x` through the punctured
neighborhood whenever `y ≠ 0`. -/
lemma helperForTheorem_25_1_tendsto_ray_to_puncturedNeighborhood
    {n : Nat} {x y : Fin n → Real} (hy : y ≠ 0) :
    Filter.Tendsto (fun t : Real => x + t • y)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhdsWithin x {z | z ≠ x}) := by
  -- The ray map is continuous at `0`.
  have hcont : ContinuousAt (fun t : Real => x + t • y) (0 : Real) := by
    fun_prop
  -- Positivity of the parameter keeps the ray in the punctured set.
  have hwithin : ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0), x + t • y ∈ ({z | z ≠ x} : Set _) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact helperForTheorem_25_1_nonzero_ray_ne (x := x) (y := y) hy ht
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ hwithin
  simpa [zero_smul] using (hcont.tendsto.mono_left nhdsWithin_le_nhds)

/-- Helper for Theorem 25.1: eventual effective-domain membership along a positive ray upgrades to
eventual membership in the punctured effective-domain filter used by `HasERealGradientAt`. -/
lemma helperForTheorem_25_1_eventually_mem_puncturedEffectiveDomain_of_eventually_mem_effectiveDomain_ray
    {n : Nat} {f : (Fin n → Real) → EReal} {x y : Fin n → Real}
    (hy : y ≠ 0)
    (hray : ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
      x + t • y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
      x + t • y ∈
        ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
  -- The source filter already enforces positivity of the parameter.
  have hpos : ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0), 0 < t := by
    simpa using
      (self_mem_nhdsWithin : Set.Ioi (0 : Real) ∈ nhdsWithin (0 : Real) (Set.Ioi 0))
  -- Combine positivity with the assumed effective-domain control along the ray.
  filter_upwards [hpos, hray] with t ht hmem
  exact ⟨helperForTheorem_25_1_nonzero_ray_ne (x := x) (y := y) hy ht, hmem⟩

/-- Helper for Theorem 25.1: under eventual finite-valued control on the ray, the ray map tends
into the punctured effective-domain neighborhood of `x`. -/
lemma helperForTheorem_25_1_tendsto_ray_to_puncturedEffectiveDomain
    {n : Nat} {f : (Fin n → Real) → EReal} {x y : Fin n → Real}
    (hy : y ≠ 0)
    (hray : ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
      x + t • y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    Filter.Tendsto (fun t : Real => x + t • y)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhdsWithin x
        ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
  -- Continuity gives convergence to `x`.
  have hcont : ContinuousAt (fun t : Real => x + t • y) (0 : Real) := by
    fun_prop
  -- Eventual finite-valuedness along the ray upgrades the target filter.
  have hwithin :
      ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
        x + t • y ∈
          ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    helperForTheorem_25_1_eventually_mem_puncturedEffectiveDomain_of_eventually_mem_effectiveDomain_ray
      (x := x) (y := y) hy hray
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ hwithin
  simpa [zero_smul] using (hcont.tendsto.mono_left nhdsWithin_le_nhds)

/-- Helper for Theorem 25.1: differentiability identifies each nonzero directional difference
quotient limit with the dot product against the chosen gradient witness. -/
lemma helperForTheorem_25_1_directionalDifferenceQuotient_tendsto_dotGradient {n : Nat}
    {f : (Fin n → Real) → EReal} {x y : Fin n → Real}
    (hf : ERealDifferentiableAt f x) (hy : y ≠ 0) :
    Filter.Tendsto (directionalDifferenceQuotientAt f x y)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds ((((erealGradientAt hf) ⬝ᵥ y : Real) : EReal))) := by
  let g : Fin n → Real := erealGradientAt hf
  have hg : HasERealGradientAt f x g := by
    simpa [g] using ERealDifferentiableAt.hasERealGradientAt (hf := hf)
  have hfinite :
      ∀ᶠ z in nhdsWithin x ({z | z ≠ x}),
        z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f ∧ f z ≠ ⊥ :=
    ERealDifferentiableAt.eventually_finiteValuedWithin_punctured (hf := hf)
  -- Reuse the general directional-limit lemma with the differentiability witness.
  simpa [g] using
    helperForTheorem_25_1_directionalDifferenceQuotient_tendsto_dotGradient_of_hasERealGradientAt
      (g := g) (y := y) hg hfinite hy

/-- Helper for Theorem 25.1: equality of all Euclidean pairings forces equality of the underlying
vectors. -/
lemma helperForTheorem_25_1_eq_of_dotProduct_eq {n : Nat} {g₁ g₂ : Fin n → Real}
    (hdot : ∀ y : Fin n → Real, g₁ ⬝ᵥ y = g₂ ⬝ᵥ y) :
    g₁ = g₂ := by
  -- Test the pairings on the standard basis vectors to recover each coordinate.
  ext j
  have hbasis := hdot (Pi.single j (1 : Real))
  simpa [dotProduct_single_one] using hbasis

/-- Helper for Theorem 25.1: differentiability identifies the upper directional derivative with
the gradient pairing, and therefore the chosen gradient is a Euclidean subgradient. -/
lemma helperForTheorem_25_1_gradient_gives_subgradient_and_directionalDerivative {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunction f) {x : Fin n → Real}
    (hdiff : ERealDifferentiableAt f x) :
    (∀ y : Fin n → Real,
      upperDirectionalDerivativeAt f x y =
        ((((erealGradientAt hdiff) ⬝ᵥ y : Real) : Real) : EReal)) ∧
      IsSubgradientAt f x (dotProductEquiv Real (Fin n) (erealGradientAt hdiff)) := by
  have hx : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    exact ERealDifferentiableAt.finiteAt (hf := hdiff)
  -- First compute the directional derivative from the directional quotient limit.
  have hdirEq :
      ∀ y : Fin n → Real,
        upperDirectionalDerivativeAt f x y =
          ((((erealGradientAt hdiff) ⬝ᵥ y : Real) : Real) : EReal) := by
    intro y
    by_cases hy : y = 0
    · -- The zero direction is handled by the general sublinearity theorem.
      rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx with
        ⟨_hdir, _hpos, _hconv, hzero, _hsymm⟩
      simp [hy, hzero]
    · -- For nonzero directions, compare the Chapter 23 limit with the differentiability limit.
      have hquotTendsto :
          Filter.Tendsto (directionalDifferenceQuotientAt f x y)
            (nhdsWithin (0 : Real) (Set.Ioi 0))
            (nhds (upperDirectionalDerivativeAt f x y)) := by
        exact (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx).1 y |>.2.1
      have hgradTendsto :
          Filter.Tendsto (directionalDifferenceQuotientAt f x y)
            (nhdsWithin (0 : Real) (Set.Ioi 0))
            (nhds ((((erealGradientAt hdiff) ⬝ᵥ y : Real) : EReal))) :=
        helperForTheorem_25_1_directionalDifferenceQuotient_tendsto_dotGradient
          (hf := hdiff) (y := y) hy
      exact tendsto_nhds_unique hquotTendsto hgradTendsto
  -- Then invoke Theorem 23.2 in the Euclidean identification.
  have hminor :
      ∀ y : Fin n → Real,
        ((((dotProductEquiv Real (Fin n) (erealGradientAt hdiff)) y : Real) : Real) : EReal) ≤
          upperDirectionalDerivativeAt f x y := by
    intro y
    simpa [dotProduct_comm] using le_of_eq (hdirEq y).symm
  have hiff :=
    (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
      f hf x hx (dotProductEquiv Real (Fin n) (erealGradientAt hdiff))).1
  have hsub :
      IsSubgradientAt f x (dotProductEquiv Real (Fin n) (erealGradientAt hdiff)) := by
    exact hiff.mpr hminor
  exact ⟨hdirEq, hsub⟩

/-- Helper for Theorem 25.1: a unique Euclidean subgradient already forces properness, interiority
of the effective domain, and a linear directional derivative formula. -/
lemma helperForTheorem_25_1_uniqueSubgradient_implies_linearDirectionalDerivative {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunction f) {x : Fin n → Real}
    (hx : f x ≠ ⊤ ∧ f x ≠ ⊥)
    (huniq : ∃! g : Fin n → Real, IsSubgradientAt f x (dotProductEquiv Real (Fin n) g)) :
    ∃ g : Fin n → Real,
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f ∧
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) ∧
        ∀ y : Fin n → Real,
          upperDirectionalDerivativeAt f x y = (((g ⬝ᵥ y : Real) : Real) : EReal) := by
  rcases huniq with ⟨g, hg, hgUnique⟩
  -- The unique witness gives a nonempty subdifferential, hence properness by Theorem 23.3.
  have hsubNonempty : Set.Nonempty (subdifferentialAt f x) := by
    exact ⟨dotProductEquiv Real (Fin n) g, hg⟩
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
    exact
      (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
        f hf x hx).1 hsubNonempty
  -- Uniqueness turns the vectorized subdifferential into a singleton, so it is bounded.
  have hpreimage_singleton :
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) = ({g} : Set (Fin n → Real)) := by
    ext v
    constructor
    · intro hv
      have hvSub : IsSubgradientAt f x (dotProductEquiv Real (Fin n) v) := by
        simpa using hv
      have hvEq : v = g := hgUnique v hvSub
      simpa [hvEq]
    · intro hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      simpa using hg
  have hbounded :
      Bornology.IsBounded ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) := by
    simpa [hpreimage_singleton] using (Bornology.isBounded_singleton (x := g))
  -- The bounded nonempty criterion from Theorem 23.4 places `x` in the interior of `dom f`.
  have h23_4 :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      f hproper x
  have hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
    exact (h23_4.2.2.1).mp ⟨hsubNonempty, hbounded⟩
  have hxri :
      x ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
    exact helperForTheorem_23_4_mem_relativeInterior_of_mem_interior hxInt
  have hdirEqSub :
      ∀ y : Fin n → Real,
        upperDirectionalDerivativeAt f x y = subdifferentialSupportAt f x y := by
    exact (h23_4.2.1 hxri).2.2.2
  -- Since the subdifferential is a singleton, its support is exactly the dot product with `g`.
  have hsubsingletonDual :
      subdifferentialAt f x = ({dotProductEquiv Real (Fin n) g} : Set (Module.Dual Real (Fin n → Real))) := by
    ext xStar
    constructor
    · intro hxStar
      let v : Fin n → Real := (dotProductEquiv Real (Fin n)).symm xStar
      have hvSub : IsSubgradientAt f x (dotProductEquiv Real (Fin n) v) := by
        simpa [v] using hxStar
      have hvEq : v = g := hgUnique v hvSub
      have hxStarEq : xStar = dotProductEquiv Real (Fin n) g := by
        calc
          xStar = dotProductEquiv Real (Fin n) v := by
            simpa [v] using (dotProductEquiv Real (Fin n)).apply_symm_apply xStar
          _ = dotProductEquiv Real (Fin n) g := by
            simpa [hvEq]
      simpa [hxStarEq]
    · intro hxStar
      rcases Set.mem_singleton_iff.mp hxStar with rfl
      exact hg
  have hsupport :
      ∀ y : Fin n → Real,
        subdifferentialSupportAt f x y = (((g ⬝ᵥ y : Real) : Real) : EReal) := by
    intro y
    rw [subdifferentialSupportAt, hsubsingletonDual]
    have himage :
        ((fun g' : Module.Dual Real (Fin n → Real) => ((g' y : Real) : EReal)) ''
            ({dotProductEquiv Real (Fin n) g} : Set (Module.Dual Real (Fin n → Real)))) =
          ({(((g ⬝ᵥ y : Real) : Real) : EReal)} : Set EReal) := by
      ext z
      constructor
      · rintro ⟨g', hg', rfl⟩
        rcases Set.mem_singleton_iff.mp hg' with rfl
        simp
      · intro hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        refine ⟨dotProductEquiv Real (Fin n) g, ?_, ?_⟩
        · simp
        · simp
    rw [himage]
    simp
  refine ⟨g, hproper, hxInt, ?_⟩
  intro y
  calc
    upperDirectionalDerivativeAt f x y = subdifferentialSupportAt f x y := hdirEqSub y
    _ = (((g ⬝ᵥ y : Real) : Real) : EReal) := hsupport y

/-- Helper for Theorem 25.1: an open set containing `x` contains a smaller closed ball around
`x`. -/
lemma helperForTheorem_25_1_exists_closedBall_subset_of_isOpen {n : Nat}
    {C : Set (Fin n → Real)} (hCopen : IsOpen C) {x : Fin n → Real} (hx : x ∈ C) :
    ∃ r : Real, 0 < r ∧ Metric.closedBall x r ⊆ C := by
  -- First choose an open ball around `x` inside `C`.
  rcases Metric.mem_nhds_iff.1 (hCopen.mem_nhds hx) with ⟨r, hrpos, hrsub⟩
  refine ⟨r / 2, by linarith [hrpos], ?_⟩
  intro y hy
  have hyBall : y ∈ Metric.ball x r := by
    have hlt : r / 2 < r := by linarith [hrpos]
    exact (Metric.closedBall_subset_ball hlt) hy
  exact hrsub hyBall

/-- Helper for Theorem 25.1: linearity of the upper directional derivative identifies `g` as the
Euclidean subgradient at `x`. -/
lemma helperForTheorem_25_1_subgradient_of_linearDirectionalDerivative {n : Nat}
    {f : (Fin n → Real) → EReal} {x g : Fin n → Real}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hdir :
      ∀ y : Fin n → Real,
        upperDirectionalDerivativeAt f x y = (((g ⬝ᵥ y : Real) : Real) : EReal)) :
    IsSubgradientAt f x (dotProductEquiv Real (Fin n) g) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := interior_subset hxInt
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    refine ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hxDom,
      ?_⟩
    exact hproper.2.2 x (by simp)
  -- Theorem 23.2 turns the linear minorant condition on directional derivatives into a
  -- subgradient statement.
  have hminor :
      ∀ y : Fin n → Real,
        ((((dotProductEquiv Real (Fin n) g) y : Real) : Real) : EReal) ≤
          upperDirectionalDerivativeAt f x y := by
    intro y
    calc
      ((((dotProductEquiv Real (Fin n) g) y : Real) : Real) : EReal) =
          (((g ⬝ᵥ y : Real) : Real) : EReal) := by
            simp
      _ ≤ upperDirectionalDerivativeAt f x y := by
            exact le_of_eq (hdir y).symm
  have hiff :=
    (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
      f hf x hxFinite (dotProductEquiv Real (Fin n) g)).1
  exact hiff.mpr hminor

/-- Helper for Theorem 25.1: interior-domain membership provides a closed ball that stays inside
the effective domain. -/
lemma helperForTheorem_25_1_exists_closedBall_subset_effectiveDomain {n : Nat}
    {f : (Fin n → Real) → EReal} {x : Fin n → Real}
    (hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ∃ ρ : Real, 0 < ρ ∧
      Metric.closedBall x ρ ⊆ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
  -- Convert the interior hypothesis into a uniform closed-ball neighborhood.
  rcases helperForTheorem_25_1_exists_closedBall_subset_of_isOpen
      (n := n) (C := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
      isOpen_interior hxInt with ⟨ρ, hρpos, hρsub⟩
  refine ⟨ρ, hρpos, ?_⟩
  intro z hz
  exact interior_subset (hρsub hz)

/-- Helper for Theorem 25.1: interior-domain membership provides a closed ball that stays inside
the interior of the effective domain. -/
lemma helperForTheorem_25_1_exists_closedBall_subset_interior_effectiveDomain {n : Nat}
    {f : (Fin n → Real) → EReal} {x : Fin n → Real}
    (hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ∃ ρ : Real, 0 < ρ ∧
      Metric.closedBall x ρ ⊆ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
  -- Reuse the open-ball extraction directly on the interior so later continuity lemmas can stay
  -- inside the finite-valued region.
  rcases helperForTheorem_25_1_exists_closedBall_subset_of_isOpen
      (n := n) (C := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
      isOpen_interior hxInt with ⟨ρ, hρpos, hρsub⟩
  exact ⟨ρ, hρpos, hρsub⟩

/-- Helper for Theorem 25.1: on the closed ball supplied by interiority, all values of `f` are
finite. -/
lemma helperForTheorem_25_1_exists_closedBall_finiteValues {n : Nat}
    {f : (Fin n → Real) → EReal} {x : Fin n → Real}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ∃ ρ : Real, 0 < ρ ∧
      ∀ z : Fin n → Real, z ∈ Metric.closedBall x ρ → f z ≠ ⊤ ∧ f z ≠ ⊥ := by
  rcases helperForTheorem_25_1_exists_closedBall_subset_effectiveDomain (f := f) hxInt with
    ⟨ρ, hρpos, hρsub⟩
  refine ⟨ρ, hρpos, ?_⟩
  intro z hz
  have hzDom : z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := hρsub hz
  exact
    ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hzDom,
      hproper.2.2 z (by simp)⟩

/-- Helper for Theorem 25.1: the dyadic scales used to compare arbitrary small secants with one
fixed remainder function. -/
noncomputable def helperForTheorem_25_1_dyadicScale (ρ : Real) : Nat → Real :=
  fun i => ρ / (2 : Real) ^ (i + 2)

/-- Helper for Theorem 25.1: the dyadic real-valued remainder family whose uniform convergence to
zero would imply differentiability. -/
noncomputable def helperForTheorem_25_1_dyadicRemainder {n : Nat}
    (f : (Fin n → Real) → EReal) (x g : Fin n → Real) (ρ : Real) :
    Nat → (Fin n → Real) → Real :=
  fun i u =>
    let τ := helperForTheorem_25_1_dyadicScale ρ i
    ((((f (x + τ • u)).toReal - (f x).toReal) - τ * (g ⬝ᵥ u)) / τ)

/-- Helper for Theorem 25.1: every dyadic comparison scale is positive. -/
lemma helperForTheorem_25_1_dyadicScale_pos {ρ : Real} (hρpos : 0 < ρ) (i : Nat) :
    0 < helperForTheorem_25_1_dyadicScale ρ i := by
  -- Positivity is immediate because the dyadic denominator is strictly positive.
  simp [helperForTheorem_25_1_dyadicScale, hρpos]

/-- Helper for Theorem 25.1: every dyadic comparison scale stays below the ambient finite-valued
radius. -/
lemma helperForTheorem_25_1_dyadicScale_le_radius {ρ : Real} (hρpos : 0 < ρ) (i : Nat) :
    helperForTheorem_25_1_dyadicScale ρ i ≤ ρ := by
  -- The denominator is at least `1`, so each dyadic step is no larger than the original radius.
  have hpow_nat : (1 : Nat) ≤ 2 ^ (i + 2) := Nat.one_le_pow (i + 2) 2 (by omega)
  have hpow_ge : (1 : Real) ≤ (2 : Real) ^ (i + 2) := by
    exact_mod_cast hpow_nat
  have hpow_pos : 0 < (2 : Real) ^ (i + 2) := by
    positivity
  rw [helperForTheorem_25_1_dyadicScale]
  exact (div_le_iff₀ hpow_pos).2 (by nlinarith [hpow_ge, hρpos])

/-- Helper for Theorem 25.1: the dyadic scales approach zero along `atTop`. -/
lemma helperForTheorem_25_1_dyadicScale_tendsto_zero {ρ : Real} :
    Filter.Tendsto (helperForTheorem_25_1_dyadicScale ρ) Filter.atTop (nhds 0) := by
  -- Rewrite the dyadic scale as a fixed multiple of a geometric sequence with ratio `1 / 2`.
  have hpow :
      Filter.Tendsto (fun i : Nat => ((1 / 2 : Real) ^ i)) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have hshift : Filter.Tendsto (fun i : Nat => i + 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_add_atTop_nat 2
  have hpowShift :
      Filter.Tendsto (fun i : Nat => ((1 / 2 : Real) ^ (i + 2))) Filter.atTop (nhds 0) :=
    hpow.comp hshift
  have hscaled :
      Filter.Tendsto (fun i : Nat => ρ * ((1 / 2 : Real) ^ (i + 2))) Filter.atTop
        (nhds (ρ * 0)) :=
    hpowShift.const_mul ρ
  simpa [helperForTheorem_25_1_dyadicScale, div_eq_mul_inv] using hscaled

/-- Helper for Theorem 25.1: directions in the closed unit ball stay inside the closed finite
ball after one dyadic step. -/
lemma helperForTheorem_25_1_step_mem_closedBall_of_mem_closedUnitBall {n : Nat}
    {x u : Fin n → Real} {ρ : Real} (hρpos : 0 < ρ) (i : Nat)
    (hu : u ∈ Metric.closedBall (0 : Fin n → Real) 1) :
    x + helperForTheorem_25_1_dyadicScale ρ i • u ∈ Metric.closedBall x ρ := by
  -- Estimate the displacement norm by `τ i * ‖u‖ ≤ τ i ≤ ρ`.
  rw [Metric.mem_closedBall]
  have hu_norm : ‖u‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  have hτnonneg : 0 ≤ helperForTheorem_25_1_dyadicScale ρ i := by
    exact le_of_lt (helperForTheorem_25_1_dyadicScale_pos hρpos i)
  have hτle : helperForTheorem_25_1_dyadicScale ρ i ≤ ρ :=
    helperForTheorem_25_1_dyadicScale_le_radius hρpos i
  have hnorm :
      ‖helperForTheorem_25_1_dyadicScale ρ i • u‖ ≤ ρ := by
    calc
      ‖helperForTheorem_25_1_dyadicScale ρ i • u‖ =
          |helperForTheorem_25_1_dyadicScale ρ i| * ‖u‖ := norm_smul _ _
      _ = helperForTheorem_25_1_dyadicScale ρ i * ‖u‖ := by
          rw [abs_of_nonneg hτnonneg]
      _ ≤ helperForTheorem_25_1_dyadicScale ρ i * 1 := by
          gcongr
      _ = helperForTheorem_25_1_dyadicScale ρ i := by
          ring
      _ ≤ ρ := hτle
  simpa [dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnorm

/-- Helper for Theorem 25.1: each dyadic remainder function is continuous on the closed unit ball
once the comparison ball stays inside the interior of the effective domain. -/
lemma helperForTheorem_25_1_remainderSequence_continuousOn_closedUnitBall {n : Nat}
    {f : (Fin n → Real) → EReal} {x g : Fin n → Real} {ρ : Real}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hρpos : 0 < ρ)
    (hρsub :
      Metric.closedBall x ρ ⊆ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ∀ i, ContinuousOn (helperForTheorem_25_1_dyadicRemainder f x g ρ i)
      (Metric.closedBall (0 : Fin n → Real) 1) := by
  have hfConv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
    simpa [ConvexFunctionOn] using hproper.1
  have hDomConv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hproper.1
  have hIntConv :
      Convex ℝ (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
    simpa using hDomConv.interior
  have hIntSub :
      interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) ⊆
        effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
    interior_subset
  have hIntRelOpen :
      euclideanRelativelyOpen n
        ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
          interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
    let C : Set (EuclideanSpace Real (Fin n)) :=
      ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
        interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    have hCopen : IsOpen C := by
      exact isOpen_interior.preimage (by fun_prop)
    have hCne : C.Nonempty := by
      refine ⟨(EuclideanSpace.equiv (Fin n) Real).symm x, ?_⟩
      simpa [C] using hxInt
    have hspanC : affineSpan Real C = ⊤ := hCopen.affineSpan_eq_top hCne
    have hriC : euclideanRelativeInterior n C = interior C := by
      -- Open nonempty subsets of `ℝ^n` are full-dimensional, so relative interior equals interior.
      apply euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ (n := n) (C := C)
      simp [hspanC]
    simpa [C, euclideanRelativelyOpen, hCopen.interior_eq, hriC]
  have hcontInt :
      ContinuousOn f (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :=
    convexFunctionOn_continuousOn_of_relOpen_effectiveDomain
      (n := n) (f := f) hfConv hIntConv hIntSub hIntRelOpen
  intro i
  have hmap :
      Set.MapsTo
        (fun u : Fin n → Real => x + helperForTheorem_25_1_dyadicScale ρ i • u)
        (Metric.closedBall (0 : Fin n → Real) 1)
        (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
    -- The dyadic step keeps every unit-ball direction inside the interior finite-valued region.
    intro u hu
    exact hρsub (helperForTheorem_25_1_step_mem_closedBall_of_mem_closedUnitBall hρpos i hu)
  have hfinite :
      ∀ u ∈ Metric.closedBall (0 : Fin n → Real) 1,
        f (x + helperForTheorem_25_1_dyadicScale ρ i • u) ≠ ⊥ ∧
          f (x + helperForTheorem_25_1_dyadicScale ρ i • u) ≠ ⊤ := by
    intro u hu
    have huInt :
        x + helperForTheorem_25_1_dyadicScale ρ i • u ∈
          interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      hmap hu
    have huDom :
        x + helperForTheorem_25_1_dyadicScale ρ i • u ∈
          effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
      interior_subset huInt
    exact
      ⟨hproper.2.2 _ (by simp),
        mem_effectiveDomain_imp_ne_top (S := Set.univ) (f := f) huDom⟩
  have hcontToReal :
      ContinuousOn
        (fun u : Fin n → Real =>
          (f (x + helperForTheorem_25_1_dyadicScale ρ i • u)).toReal)
        (Metric.closedBall (0 : Fin n → Real) 1) := by
    refine (EReal.continuousOn_toReal).comp (hcontInt.comp (by fun_prop) hmap) ?_
    intro u hu
    have hfi := hfinite u hu
    simp [Set.mem_compl_iff, Set.mem_insert_iff, hfi.1, hfi.2]
  have hlin :
      Continuous (fun u : Fin n → Real =>
        helperForTheorem_25_1_dyadicScale ρ i * (g ⬝ᵥ u)) := by
    -- The affine correction term is a fixed scalar multiple of a continuous linear functional.
    fun_prop
  simpa [helperForTheorem_25_1_dyadicRemainder] using
    (((hcontToReal.sub continuousOn_const).sub hlin.continuousOn).div_const
      (helperForTheorem_25_1_dyadicScale ρ i))

/-- Helper for Theorem 25.1: for a fixed direction in the closed unit ball, the dyadic remainder
sequence is antitone, nonnegative, and tends to `0`. -/
lemma helperForTheorem_25_1_remainderSequence_antitone_nonneg_tendsto_zero {n : Nat}
    {f : (Fin n → Real) → EReal} {x g u : Fin n → Real} {ρ : Real}
    (hf : ConvexFunction f)
    (hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥)
    (hρpos : 0 < ρ)
    (hfiniteStep :
      ∀ i,
        f (x + helperForTheorem_25_1_dyadicScale ρ i • u) ≠ ⊤ ∧
          f (x + helperForTheorem_25_1_dyadicScale ρ i • u) ≠ ⊥)
    (hdiru :
      upperDirectionalDerivativeAt f x u = (((g ⬝ᵥ u : Real) : Real) : EReal))
    (hsub : IsSubgradientAt f x (dotProductEquiv Real (Fin n) g)) :
    Antitone (fun i => helperForTheorem_25_1_dyadicRemainder f x g ρ i u) ∧
      (∀ i, 0 ≤ helperForTheorem_25_1_dyadicRemainder f x g ρ i u) ∧
      Filter.Tendsto (fun i => helperForTheorem_25_1_dyadicRemainder f x g ρ i u)
        Filter.atTop (nhds 0) := by
  let τ : Nat → Real := helperForTheorem_25_1_dyadicScale ρ
  let Q : Nat → Real := fun i =>
    ((f (x + τ i • u)).toReal - (f x).toReal) / τ i
  have hconvDir :=
    convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite
  rcases hconvDir with ⟨hquot, _hposDir, _hconvDir, _hzeroDir, _hsymmDir⟩
  have hR_eq : ∀ i, helperForTheorem_25_1_dyadicRemainder f x g ρ i u = Q i - g ⬝ᵥ u := by
    intro i
    have hτne : τ i ≠ 0 := ne_of_gt (helperForTheorem_25_1_dyadicScale_pos hρpos i)
    -- Separate the affine correction term from the finite quotient.
    change ((((f (x + τ i • u)).toReal - (f x).toReal) - τ i * (g ⬝ᵥ u)) / τ i) =
      (((f (x + τ i • u)).toReal - (f x).toReal) / τ i - g ⬝ᵥ u)
    field_simp [hτne]
  have hQ_eq_quot :
      ∀ i, directionalDifferenceQuotientAt f x u (τ i) = ((Q i : Real) : EReal) := by
    intro i
    have hfi := hfiniteStep i
    -- At every dyadic step the quotient is finite, so it is exactly the coercion of the real
    -- quotient built from `toReal`.
    simp [Q, τ, directionalDifferenceQuotientAt, EReal.coe_div, EReal.coe_sub,
      EReal.coe_toReal hfi.1 hfi.2, EReal.coe_toReal hxFinite.1 hxFinite.2]
  have hantitoneQ : Antitone Q := by
    intro i j hij
    have hτjPos : 0 < τ j := helperForTheorem_25_1_dyadicScale_pos hρpos j
    have hτiPos : 0 < τ i := helperForTheorem_25_1_dyadicScale_pos hρpos i
    have hijPowNat : 2 ^ (i + 2) ≤ 2 ^ (j + 2) := by
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hijPow : (2 : Real) ^ (i + 2) ≤ (2 : Real) ^ (j + 2) := by
      exact_mod_cast hijPowNat
    have hτanti : τ j ≤ τ i := by
      dsimp [τ, helperForTheorem_25_1_dyadicScale]
      exact div_le_div_of_nonneg_left (le_of_lt hρpos)
        (show 0 < (2 : Real) ^ (i + 2) by positivity) hijPow
    have hmonoE :
        directionalDifferenceQuotientAt f x u (τ j) ≤
          directionalDifferenceQuotientAt f x u (τ i) :=
      (hquot u).1 hτjPos hτiPos hτanti
    have hmonoReal :
        Q j ≤ Q i := by
      exact_mod_cast (show ((Q j : Real) : EReal) ≤ ((Q i : Real) : EReal) by
        simpa [hQ_eq_quot j, hQ_eq_quot i] using hmonoE)
    exact hmonoReal
  have hnonneg : ∀ i, 0 ≤ helperForTheorem_25_1_dyadicRemainder f x g ρ i u := by
    intro i
    have hτPos : 0 < τ i := helperForTheorem_25_1_dyadicScale_pos hρpos i
    have hlowerE :
        (((g ⬝ᵥ u : Real) : Real) : EReal) ≤ directionalDifferenceQuotientAt f x u (τ i) :=
      helperForTheorem_23_2_differenceQuotient_lowerBound_of_subgradient
        f x hxFinite (dotProductEquiv Real (Fin n) g) hsub u hτPos
    have hlowerReal : g ⬝ᵥ u ≤ Q i := by
      exact_mod_cast (show (((g ⬝ᵥ u : Real) : Real) : EReal) ≤ ((Q i : Real) : EReal) by
        simpa [hQ_eq_quot i] using hlowerE)
    rw [hR_eq i]
    linarith
  have hτWithin :
      Filter.Tendsto τ Filter.atTop (nhdsWithin (0 : Real) (Set.Ioi 0)) := by
    -- The dyadic steps approach `0` while remaining positive.
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within τ
      helperForTheorem_25_1_dyadicScale_tendsto_zero ?_
    filter_upwards with i
    exact helperForTheorem_25_1_dyadicScale_pos hρpos i
  have hquotAlongTau :
      Filter.Tendsto (fun i => directionalDifferenceQuotientAt f x u (τ i))
        Filter.atTop (nhds (((g ⬝ᵥ u : Real) : Real) : EReal)) := by
    simpa [hdiru] using (hquot u).2.1.comp hτWithin
  have hQtendsto :
      Filter.Tendsto Q Filter.atTop (nhds (g ⬝ᵥ u)) := by
    have hQcoe :
        Filter.Tendsto (fun i => ((Q i : Real) : EReal)) Filter.atTop
          (nhds ((((g ⬝ᵥ u : Real) : Real) : EReal))) := by
      refine Filter.Tendsto.congr' ?_ hquotAlongTau
      filter_upwards with i
      simpa [hQ_eq_quot i]
    exact (EReal.tendsto_coe).1 hQcoe
  have hRtendsto :
      Filter.Tendsto (fun i => helperForTheorem_25_1_dyadicRemainder f x g ρ i u)
        Filter.atTop (nhds 0) := by
    -- Subtract the identified directional-derivative limit to make the remainder vanish.
    have hsubTendsto :
        Filter.Tendsto (fun i => Q i - g ⬝ᵥ u) Filter.atTop (nhds (g ⬝ᵥ u - g ⬝ᵥ u)) :=
      hQtendsto.sub tendsto_const_nhds
    convert hsubTendsto using 1
    · funext i
      exact hR_eq i
    · simp
  have hantitoneR : Antitone (fun i => helperForTheorem_25_1_dyadicRemainder f x g ρ i u) := by
    intro i j hij
    change helperForTheorem_25_1_dyadicRemainder f x g ρ j u ≤
      helperForTheorem_25_1_dyadicRemainder f x g ρ i u
    rw [hR_eq j, hR_eq i]
    exact sub_le_sub_right (hantitoneQ hij) (g ⬝ᵥ u)
  exact ⟨hantitoneR, hnonneg, hRtendsto⟩

/-- Helper for Theorem 25.1: Dini's theorem upgrades the dyadic remainder sequence to uniform
convergence on the closed unit ball. -/
lemma helperForTheorem_25_1_remainderSequence_tendstoUniformlyOn_closedUnitBall {n : Nat}
    {f : (Fin n → Real) → EReal} {x g : Fin n → Real} {ρ : Real}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hρpos : 0 < ρ)
    (hρsub :
      Metric.closedBall x ρ ⊆ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hdir :
      ∀ y : Fin n → Real,
        upperDirectionalDerivativeAt f x y = (((g ⬝ᵥ y : Real) : Real) : EReal))
    (hsub : IsSubgradientAt f x (dotProductEquiv Real (Fin n) g)) :
    TendstoUniformlyOn (helperForTheorem_25_1_dyadicRemainder f x g ρ) (fun _ => 0)
      Filter.atTop (Metric.closedBall (0 : Fin n → Real) 1) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := interior_subset hxInt
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    refine ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hxDom,
      hproper.2.2 x (by simp)⟩
  have hcont :
      ∀ i, ContinuousOn (helperForTheorem_25_1_dyadicRemainder f x g ρ i)
        (Metric.closedBall (0 : Fin n → Real) 1) :=
    helperForTheorem_25_1_remainderSequence_continuousOn_closedUnitBall
      (f := f) (x := x) (g := g) (ρ := ρ) hproper hxInt hρpos hρsub
  have hanti :
      ∀ u ∈ Metric.closedBall (0 : Fin n → Real) 1,
        Antitone fun i => helperForTheorem_25_1_dyadicRemainder f x g ρ i u := by
    intro u hu
    have hfiniteStep :
        ∀ i,
          f (x + helperForTheorem_25_1_dyadicScale ρ i • u) ≠ ⊤ ∧
            f (x + helperForTheorem_25_1_dyadicScale ρ i • u) ≠ ⊥ := by
      intro i
      have hstepInt :
          x + helperForTheorem_25_1_dyadicScale ρ i • u ∈
            interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
        hρsub (helperForTheorem_25_1_step_mem_closedBall_of_mem_closedUnitBall hρpos i hu)
      have hstepDom :
          x + helperForTheorem_25_1_dyadicScale ρ i • u ∈
            effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
        interior_subset hstepInt
      exact
        ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hstepDom,
          hproper.2.2 _ (by simp)⟩
    exact
      (helperForTheorem_25_1_remainderSequence_antitone_nonneg_tendsto_zero
        (f := f) (x := x) (g := g) (u := u) (ρ := ρ) hf hxFinite hρpos hfiniteStep
        (hdir u) hsub).1
  have hpoint :
      ∀ u ∈ Metric.closedBall (0 : Fin n → Real) 1,
        Filter.Tendsto (fun i => helperForTheorem_25_1_dyadicRemainder f x g ρ i u)
          Filter.atTop (nhds 0) := by
    intro u hu
    have hfiniteStep :
        ∀ i,
          f (x + helperForTheorem_25_1_dyadicScale ρ i • u) ≠ ⊤ ∧
            f (x + helperForTheorem_25_1_dyadicScale ρ i • u) ≠ ⊥ := by
      intro i
      have hstepInt :
          x + helperForTheorem_25_1_dyadicScale ρ i • u ∈
            interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
        hρsub (helperForTheorem_25_1_step_mem_closedBall_of_mem_closedUnitBall hρpos i hu)
      have hstepDom :
          x + helperForTheorem_25_1_dyadicScale ρ i • u ∈
            effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
        interior_subset hstepInt
      exact
        ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hstepDom,
          hproper.2.2 _ (by simp)⟩
    exact
      (helperForTheorem_25_1_remainderSequence_antitone_nonneg_tendsto_zero
        (f := f) (x := x) (g := g) (u := u) (ρ := ρ) hf hxFinite hρpos hfiniteStep
        (hdir u) hsub).2.2
  exact Antitone.tendstoUniformlyOn_of_forall_tendsto
    (isCompact_closedBall (0 : Fin n → Real) 1) hcont hanti continuousOn_const hpoint

end Section25
end Chap05
