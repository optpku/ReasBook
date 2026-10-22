/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ProbabilityTheory
open MeasureTheory ProbabilityTheory

universe u v

variable {G : Type u} [Group G] [Fintype G]
variable {Ω : Type v} [MeasurableSpace Ω] [MulAction G Ω] [MeasurableConstSMul G Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] [SMulInvariantMeasure G Ω P]

/-- Helper for Exercise 20.1.1: `orbitAverage Y` is the finite average of `Y` over the group
orbit of a point. -/
noncomputable def orbitAverage (Y : Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ ((Fintype.card G : ℝ)⁻¹) * ∑ g : G, Y (g • ω)

/-- Helper for Exercise 20.1.1: the orbit average is pointwise invariant under the group action. -/
lemma orbitAverage_comp_smul_eq (Y : Ω → ℝ) (a : G) (ω : Ω) :
    orbitAverage (G := G) Y (a • ω) = orbitAverage (G := G) Y ω := by
  -- Reindex the sum by right multiplication to absorb the extra action by `a`.
  rw [orbitAverage, orbitAverage]
  congr 1
  simpa [mul_smul] using
    (Fintype.sum_equiv (Equiv.mulRight a) (fun g : G ↦ Y (g • (a • ω)))
      (fun g : G ↦ Y (g • ω)) fun g ↦ by simp [mul_smul])

/-- Helper for Exercise 20.1.1: a measurable orbit average is measurable for the sigma-algebra
of sets invariant under every group element. -/
lemma measurable_orbitAverage_groupInvariants {Y : Ω → ℝ} (hY : Measurable Y) :
    Measurable[⨅ g : G, MeasurableSpace.invariants (g • ·)] (orbitAverage (G := G) Y) := by
  -- First record ordinary measurability of the finite average.
  have hOrbitMeas : Measurable (orbitAverage (G := G) Y) := by
    fun_prop [orbitAverage]
  -- Then check invariance for each generating action separately.
  intro s hs
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  exact ((MeasurableSpace.measurable_invariants_dom).2 ⟨hOrbitMeas, fun t ht ↦ by
    ext ω
    simp [Function.comp, orbitAverage_comp_smul_eq (G := G) (Y := Y) (a := a)]⟩) hs

/-- Helper for Exercise 20.1.1: the orbit average of an integrable function is integrable. -/
lemma integrable_orbitAverage {Y : Ω → ℝ} (hY : Integrable Y P) :
    Integrable (orbitAverage (G := G) Y) P := by
  -- Each translate remains integrable because every group element acts measure-preservingly.
  have hTranslate : ∀ g : G, Integrable (fun ω ↦ Y (g • ω)) P := fun g ↦
    (measurePreserving_smul g P).integrable_comp_of_integrable hY
  -- Finite sums and scalar multiples preserve integrability.
  simpa [orbitAverage] using
    (integrable_finset_sum (Finset.univ) fun g _ ↦ hTranslate g).const_mul
      ((Fintype.card G : ℝ)⁻¹)

/-- Helper for Exercise 20.1.1: translating an integral over an invariant set does not change
its value. -/
lemma setIntegral_comp_smul_eq_of_invariant (a : G) {Y : Ω → ℝ} {s : Set Ω}
    (hs : MeasurableSet[MeasurableSpace.invariants (a • ·)] s) :
    ∫ ω in s, Y (a • ω) ∂P = ∫ ω in s, Y ω ∂P := by
  -- Unpack the invariance condition into ambient measurability and set equality.
  rcases (MeasurableSpace.measurableSet_invariants.mp hs) with ⟨hsMeas, hsInv⟩
  have hsMem : ∀ ω : Ω, ω ∈ s ↔ a • ω ∈ s := fun ω ↦ by
    change ω ∈ s ↔ ω ∈ (a • ·) ⁻¹' s
    rw [hsInv]
  have hIndicator :
      (fun ω ↦ s.indicator Y (a • ω)) = s.indicator (fun ω ↦ Y (a • ω)) := by
    -- Rewrite the translated indicator using invariance of the set `s`.
    funext ω
    by_cases hω : ω ∈ s
    · have haω : a • ω ∈ s := (hsMem ω).1 hω
      simp [Set.indicator_of_mem, hω, haω]
    · have haω : a • ω ∉ s := by
        exact mt (hsMem ω).2 hω
      simp [hω, haω]
  calc
    ∫ ω in s, Y (a • ω) ∂P = ∫ ω, s.indicator (fun ω ↦ Y (a • ω)) ω ∂P := by
      rw [integral_indicator hsMeas]
    _ = ∫ ω, s.indicator Y (a • ω) ∂P := by
      simp [hIndicator]
    _ = ∫ ω, s.indicator Y ω ∂P := by
      simpa [Function.comp] using integral_smul_eq_self (μ := P) (f := s.indicator Y) (g := a)
    _ = ∫ ω in s, Y ω ∂P := by
      rw [integral_indicator hsMeas]

/-- Helper for Exercise 20.1.1: on every group-invariant measurable set, the orbit average has
the same integral as the original integrable function. -/
lemma setIntegral_orbitAverage_eq {Y : Ω → ℝ} (hY : Integrable Y P) {s : Set Ω}
    (hs : MeasurableSet[⨅ g : G, MeasurableSpace.invariants (g • ·)] s) :
    ∫ ω in s, orbitAverage (G := G) Y ω ∂P = ∫ ω in s, Y ω ∂P := by
  -- Restricting an integrable translate to `s` keeps it integrable, so linearity applies.
  have hTranslateInt : ∀ a : G, Integrable (fun ω ↦ Y (a • ω)) (P.restrict s) := fun a ↦
    ((measurePreserving_smul a P).integrable_comp_of_integrable hY).integrableOn
  have hInvSet : ∀ a : G, MeasurableSet[MeasurableSpace.invariants (a • ·)] s := fun a ↦
    (MeasurableSpace.measurableSet_iInf.mp hs) a
  have hCard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    ∫ ω in s, orbitAverage (G := G) Y ω ∂P
        = ((Fintype.card G : ℝ)⁻¹) * ∫ ω, ∑ a : G, Y (a • ω) ∂P.restrict s := by
            simpa [orbitAverage] using
              (integral_const_mul ((Fintype.card G : ℝ)⁻¹)
                (fun ω ↦ ∑ a : G, Y (a • ω)) (μ := P.restrict s))
    _ = ((Fintype.card G : ℝ)⁻¹) * ∑ a : G, ∫ ω in s, Y (a • ω) ∂P := by
          rw [integral_finset_sum _ fun a _ ↦ hTranslateInt a]
    _ = ((Fintype.card G : ℝ)⁻¹) * ∑ a : G, ∫ ω in s, Y ω ∂P := by
          congr 2 with a
          exact setIntegral_comp_smul_eq_of_invariant (P := P) (Y := Y) (a := a) (hInvSet a)
    _ = ∫ ω in s, Y ω ∂P := by
          simp [hCard]

/-- Helper for Exercise 20.1.1: the orbit average preserves almost-everywhere equality. -/
lemma orbitAverage_congr_ae {Y Z : Ω → ℝ} (hYZ : Y =ᵐ[P] Z) :
    orbitAverage (G := G) Y =ᵐ[P] orbitAverage (G := G) Z := by
  have hTranslateAe :
      ∀ g : G, (fun ω ↦ Y (g • ω)) =ᵐ[P] fun ω ↦ Z (g • ω) := fun g ↦
        Measure.QuasiMeasurePreserving.ae_eq_comp
          (measurePreserving_smul g P).quasiMeasurePreserving hYZ
  have hSumAeFinset :
      ∀ s : Finset G,
        ((fun ω ↦ Finset.sum s (fun g ↦ Y (g • ω))) =ᵐ[P]
          (fun ω ↦ Finset.sum s (fun g ↦ Z (g • ω)))) := by
    classical
    -- Sum the translated almost-everywhere equalities over the finite group.
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp
    | insert g s hg hs =>
        simpa [Finset.sum_insert, hg] using (hTranslateAe g).add hs
  have hSumAe : (fun ω ↦ ∑ g : G, Y (g • ω)) =ᵐ[P] fun ω ↦ ∑ g : G, Z (g • ω) :=
    hSumAeFinset Finset.univ
  -- The scalar factor in the average is deterministic, so the sum equality is enough.
  filter_upwards [hSumAe] with ω hω
  simp [orbitAverage, hω]

/-- Helper for Exercise 20.1.1: a measurable representative with the right orbit-average
integrals is almost surely the conditional expectation on the invariant sigma-algebra. -/
lemma orbitAverage_mk_ae_eq_condExp {X Xm : Ω → ℝ} (hX : Integrable X P)
    (hXm_ae : Xm =ᵐ[P] X) (hXm_meas : Measurable Xm) :
    orbitAverage (G := G) Xm =ᵐ[P]
      P[X | ⨅ g : G, MeasurableSpace.invariants (g • ·)] := by
  let mΩ : MeasurableSpace Ω := inferInstance
  have hXm_int : Integrable Xm P := hX.congr hXm_ae.symm
  have hm : (⨅ g : G, MeasurableSpace.invariants (g • ·)) ≤ mΩ := by
    -- Any invariant-measurable set is measurable in the ambient sigma-algebra.
    intro s hs
    exact
      (MeasurableSpace.measurableSet_invariants.mp
        ((MeasurableSpace.measurableSet_iInf.mp hs) (1 : G))).1
  have hOrbitMeas :
      AEStronglyMeasurable[⨅ g : G, MeasurableSpace.invariants (g • ·)]
        (orbitAverage (G := G) Xm) P :=
    (measurable_orbitAverage_groupInvariants (G := G) (Y := Xm) hXm_meas).aestronglyMeasurable
  have hOrbitInt : Integrable (orbitAverage (G := G) Xm) P :=
    integrable_orbitAverage (G := G) (P := P) hXm_int
  -- Uniqueness of conditional expectation reduces the theorem to the set-integral identity.
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hX
    (fun s _ _ ↦ hOrbitInt.integrableOn) ?_ hOrbitMeas
  intro s hs hμs
  have hsMeas : MeasurableSet s := hm _ hs
  calc
    ∫ ω in s, orbitAverage (G := G) Xm ω ∂P = ∫ ω in s, Xm ω ∂P := by
      exact setIntegral_orbitAverage_eq (G := G) (P := P) hXm_int hs
    _ = ∫ ω in s, X ω ∂P := by
      refine setIntegral_congr_ae hsMeas ?_
      filter_upwards [hXm_ae] with ω hω hωs
      exact hω

-- Proof sketch: the finite average `ω ↦ (1 / |G|) ∑ g, X (g • ω)` is invariant under each group
-- element because left multiplication permutes `G`. The owner abstraction
-- `SMulInvariantMeasure G Ω P` yields measure preservation of every map `g • ·`, and the ambient
-- probability measure hypothesis keeps the conditional expectation onto
-- `⨅ g, MeasurableSpace.invariants (g • ·)` in the sigma-finite regime. Hence this average has the
-- same integrals as `X` on every invariant event, and uniqueness of conditional expectation
-- identifies it almost everywhere with `P[X | ...]`.
/-- Exercise 20.1.1: on a probability space with a finite group action by measure-preserving
measurable maps, the conditional expectation of an integrable real-valued function onto the
sigma-algebra of sets invariant under every group element is almost surely its average over the
group orbit. -/
theorem condExp_group_invariants_ae_eq_group_average
    {X : Ω → ℝ} (hX : Integrable X P) :
    P[X | ⨅ g : G, MeasurableSpace.invariants (g • ·)] =ᵐ[P]
      fun ω ↦ ((Fintype.card G : ℝ)⁻¹) * ∑ g : G, X (g • ω) := by
  let Xm : Ω → ℝ := hX.aestronglyMeasurable.mk X
  have hXm_ae : Xm =ᵐ[P] X := (show X =ᵐ[P] Xm from hX.aestronglyMeasurable.ae_eq_mk).symm
  have hXm_meas : Measurable Xm := show Measurable Xm from hX.aestronglyMeasurable.measurable_mk
  -- Use a measurable representative to invoke conditional-expectation uniqueness, then transfer
  -- back to the original function by almost-everywhere equality of orbit averages.
  simpa [orbitAverage] using
    (orbitAverage_mk_ae_eq_condExp (G := G) (P := P) hX hXm_ae hXm_meas).symm.trans
      (orbitAverage_congr_ae (G := G) (P := P) hXm_ae)
