/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_13

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

variable {E : Type u}

/-- The electrical current induced by a potential `u` on the conductance network `C`, given by
Ohm's law `I(x,y) = C(x,y) (u(x) - u(y))`. -/
def electricalCurrent (C : E → E → ℝ≥0∞) (u : E → ℝ) : E → E → ℝ :=
  fun x y ↦ (C x y).toReal * (u x - u y)

-- Proof sketch: unfold `electricalCurrent`; evaluating the induced current at `(x,y)` gives the
-- Ohm-law expression `(C x y).toReal * (u x - u y)`.
/-- Evaluating the current induced by `u` gives the Ohm-law formula at the ordered edge
`(x,y)`. -/
@[simp]
theorem electricalCurrent_apply (C : E → E → ℝ≥0∞) (u : E → ℝ) (x y : E) :
    electricalCurrent C u x y = (C x y).toReal * (u x - u y) := rfl

section

variable [Fintype E]

/-- Helper for Theorem 19.15: the total conductance at every state of a weighted random walk is
nonzero. -/
private lemma conductance_ne_zero_at
    {p C : E → E → ℝ≥0∞} [hWalk : IsRandomWalkWithWeights p C] (x : E) :
    conductance C x ≠ 0 := by
  intro hx0
  have hC_zero : ∀ y : E, C x y = 0 := by
    intro y
    have hle : C x y ≤ conductance C x := by
      simpa [conductance] using (ENNReal.le_tsum y : C x y ≤ ∑' z : E, C x z)
    rw [hx0] at hle
    exact le_antisymm hle bot_le
  have hp_zero : ∀ y : E, p x y = 0 := by
    intro y
    rw [hWalk.transition_eq, hC_zero y, hx0]
    simp
  have hsum_zero : ∑ y : E, p x y = 0 := by
    simp [hp_zero]
  have hstochastic : ∑' y : E, p x y = 1 := hWalk.isStochastic x
  have hstochastic' : ∑ y : E, p x y = 1 := by
    simpa using hstochastic
  rw [hsum_zero] at hstochastic'
  norm_num at hstochastic'

/-- Helper for Theorem 19.15: the Kirchhoff law for an electrical potential is exactly the
weighted one-step averaging identity for the associated random walk. -/
private lemma electricalPotential_average_eq
    {p C : E → E → ℝ≥0∞} [hWalk : IsRandomWalkWithWeights p C]
    {A : Set E} {u : E → ℝ} (hu : IsFlowOutside A (electricalCurrent C u)) {x : E} (hx : x ∉ A) :
    u x = ∑ y : E, (p x y).toReal * u y := by
  have hnet_zero : netFlowAt (electricalCurrent C u) x = 0 := hu.netFlowAt_eq_zero hx
  have hconductance_lt_top : conductance C x < ∞ := hWalk.conductance_lt_top x
  have hconductance_ne_zero : conductance C x ≠ 0 := conductance_ne_zero_at (p := p) (C := C) x
  have hconductance_toReal_ne_zero : (conductance C x).toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨hconductance_ne_zero, hconductance_lt_top.ne⟩
  have hentry_ne_top : ∀ y : E, C x y ≠ ∞ := by
    intro y
    apply ne_of_lt
    have hle : C x y ≤ conductance C x := by
      simpa [conductance] using (ENNReal.le_tsum y : C x y ≤ ∑' z : E, C x z)
    exact lt_of_le_of_lt hle hconductance_lt_top
  have hconductance_sum :
      ∑ y : E, (C x y).toReal = (conductance C x).toReal := by
    -- Proof comment: on a finite state space, the total conductance is the finite row sum.
    simpa [conductance] using
      (ENNReal.toReal_sum (s := Finset.univ) (f := fun y : E ↦ C x y)
        (fun y _ ↦ hentry_ne_top y)).symm
  have hrow_zero :
      ∑ y : E, (C x y).toReal * (u x - u y) = 0 := by
    -- Proof comment: unfold the net-flow identity at `x` into the explicit Ohm-law row sum.
    simpa [netFlowAt, electricalCurrent] using hnet_zero
  have hrow_expanded :
      (∑ y : E, (C x y).toReal * u x) - ∑ y : E, (C x y).toReal * u y = 0 := by
    calc
      (∑ y : E, (C x y).toReal * u x) - ∑ y : E, (C x y).toReal * u y
          = ∑ y : E, ((C x y).toReal * u x - (C x y).toReal * u y) := by
              rw [← Finset.sum_sub_distrib]
      _ = ∑ y : E, (C x y).toReal * (u x - u y) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            ring
      _ = 0 := hrow_zero
  have hweighted :
      (conductance C x).toReal * u x = ∑ y : E, (C x y).toReal * u y := by
    -- Proof comment: collect the `u x` terms on the left and rewrite their coefficient as the
    -- total conductance at `x`.
    calc
      (conductance C x).toReal * u x = (∑ y : E, (C x y).toReal) * u x := by
            rw [hconductance_sum]
      _ = ∑ y : E, (C x y).toReal * u x := by
            rw [Finset.sum_mul]
      _ = ∑ y : E, (C x y).toReal * u y := by
            linarith [hrow_expanded]
  calc
    u x = ((conductance C x).toReal)⁻¹ * ((conductance C x).toReal * u x) := by
            field_simp [hconductance_toReal_ne_zero]
    _ = ((conductance C x).toReal)⁻¹ * ∑ y : E, (C x y).toReal * u y := by
          rw [hweighted]
    _ = ∑ y : E, (((conductance C x).toReal)⁻¹ * (C x y).toReal) * u y := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro y hy
          ring
    _ = ∑ y : E, (p x y).toReal * u y := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [hWalk.transition_eq, ENNReal.toReal_div]
          ring

/-- Helper for Theorem 19.15: a positive singleton transition from a global maximizer of a
harmonic function preserves the maximal value. -/
private lemma value_eq_of_positiveTransition_from_globalMaximum
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p C : E → E → ℝ≥0∞} [hWalk : IsRandomWalkWithWeights p C]
    {A : Set E} {f : E → ℝ} {x y : E}
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f) (hx : x ∉ A)
    (hmax : ∀ z : E, f z ≤ f x)
    (hxy : 0 < (discreteMatrixKernel p) x ({y} : Set E)) :
    f y = f x := by
  have hp_ne_top : ∀ z : E, p x z ≠ ∞ := by
    intro z
    apply ne_of_lt
    have hle : p x z ≤ ∑' w : E, p x w := ENNReal.le_tsum z
    have hrow : ∑' w : E, p x w = 1 := hWalk.isStochastic x
    rw [hrow] at hle
    exact lt_of_le_of_lt hle (by simp)
  have hprob_sum : ∑ z : E, (p x z).toReal = 1 := by
    -- Proof comment: the stochastic row sum becomes a real-valued probability sum.
    calc
      ∑ z : E, (p x z).toReal = (∑ z : E, p x z).toReal := by
            symm
            exact ENNReal.toReal_sum (s := Finset.univ) (f := fun z : E ↦ p x z)
              (fun z _ ↦ hp_ne_top z)
      _ = 1 := by
            simpa using congrArg ENNReal.toReal (hWalk.isStochastic x)
  letI : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel p hWalk.isStochastic
  rcases hf hx with ⟨_, hharmonic⟩
  have haverage : f x = ∑ z : E, (p x z).toReal * f z := by
    have hsum :
        Summable (fun z : E ↦ (p x z).toReal * ‖f z‖) := Summable.of_finite
    -- Proof comment: replace the Bochner integral by the textbook rowwise series.
    rw [integral_discreteMatrixKernel_eq_tsum p hWalk.isStochastic f x hsum] at hharmonic
    simpa using hharmonic
  have hgap_sum :
      ∑ z : E, (p x z).toReal * (f x - f z) = 0 := by
    calc
      ∑ z : E, (p x z).toReal * (f x - f z)
          = ∑ z : E, ((p x z).toReal * f x - (p x z).toReal * f z) := by
              refine Finset.sum_congr rfl ?_
              intro z hz
              ring
      _ = (∑ z : E, (p x z).toReal * f x) - ∑ z : E, (p x z).toReal * f z := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ z : E, (p x z).toReal) * f x - ∑ z : E, (p x z).toReal * f z := by
            rw [← Finset.sum_mul]
      _ = 0 := by
            rw [hprob_sum]
            linarith [haverage]
  have hy_not_lt : ¬ f y < f x := by
    intro hy_lt
    have hpxy_pos : 0 < (p x y).toReal := by
      have hpxy : 0 < p x y := by
        rw [discreteMatrixKernel_apply_singleton p y x] at hxy
        exact hxy
      exact ENNReal.toReal_pos hpxy.ne' (hp_ne_top y)
    have hterm_pos : 0 < (p x y).toReal * (f x - f y) := by
      exact mul_pos hpxy_pos (sub_pos.mpr hy_lt)
    let g : E → ℝ := fun z ↦ (p x z).toReal * (f x - f z)
    have hg_nonneg : ∀ z : E, 0 ≤ g z := by
      intro z
      exact mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (hmax z))
    have hterm_le : g y ≤ ∑ z : E, g z := by
      simpa [g] using Finset.single_le_sum (fun z _ ↦ hg_nonneg z) (Finset.mem_univ y)
    have hsum_pos : 0 < ∑ z : E, (p x z).toReal * (f x - f z) :=
      lt_of_lt_of_le hterm_pos hterm_le
    rw [hgap_sum] at hsum_pos
    exact lt_irrefl _ hsum_pos
  exact le_antisymm (hmax y) (not_lt.mp hy_not_lt)

/-- Helper for Theorem 19.15: a positive `(n + 1)`-step singleton mass factors through some
positive first step and positive `n`-step singleton mass. -/
private lemma exists_intermediate_of_powSingletonMass_pos
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} {x y : E} {n : ℕ}
    (hxy : 0 < ((discreteMatrixKernel p) ^ (n + 1)) x ({y} : Set E)) :
    ∃ z : E, 0 < ((discreteMatrixKernel p) ^ n) x ({z} : Set E) ∧
      0 < (discreteMatrixKernel p) z ({y} : Set E) := by
  let κ := discreteMatrixKernel p
  rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ (MeasurableSet.singleton y),
    MeasureTheory.lintegral_fintype] at hxy
  have hsum_ne_zero :
      ∑ z : E, (κ z ({y} : Set E)) * ((κ ^ n) x) ({z} : Set E) ≠ 0 := ne_of_gt hxy
  obtain ⟨z, _, hz_ne_zero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne_zero
  have hz_factors :
      κ z ({y} : Set E) ≠ 0 ∧ ((κ ^ n) x) ({z} : Set E) ≠ 0 := by
    constructor
    · intro hz0
      exact hz_ne_zero (by rw [hz0, zero_mul])
    · intro hz0
      exact hz_ne_zero (by rw [hz0, mul_zero])
  exact ⟨z, bot_lt_iff_ne_bot.mpr hz_factors.2, bot_lt_iff_ne_bot.mpr hz_factors.1⟩

/-- Helper for Theorem 19.15: if a set is closed under positive one-step transitions, then every
state reached with positive `n`-step singleton mass from a point in the set still lies in it. -/
private lemma mem_maxSet_of_powSingletonMass_pos_of_stepClosed
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} {S : Set E} {x y : E}
    (hx : x ∈ S)
    (hstep :
      ∀ ⦃a b : E⦄, a ∈ S → 0 < (discreteMatrixKernel p) a ({b} : Set E) → b ∈ S)
    {n : ℕ} (hxy : 0 < ((discreteMatrixKernel p) ^ n) x ({y} : Set E)) :
    y ∈ S := by
  induction n generalizing x y with
  | zero =>
      by_cases hyx : y = x
      · simpa [hyx] using hx
      · have hzero : ((discreteMatrixKernel p ^ 0) x) ({y} : Set E) = 0 := by
          have hxnot : x ∉ ({y} : Set E) := by
            simpa [Set.mem_singleton_iff, eq_comm] using hyx
          change (Kernel.id x) ({y} : Set E) = 0
          rw [Kernel.id_apply, Measure.dirac_apply' _ (MeasurableSet.singleton y)]
          simp [hxnot]
        rw [hzero] at hxy
        exact (not_lt_of_ge bot_le hxy).elim
  | succ n ih =>
      rcases exists_intermediate_of_powSingletonMass_pos (p := p) hxy with ⟨z, hxz, hzy⟩
      have hzS : z ∈ S := ih hx hxz
      exact hstep hzS hzy

/-- Helper for Theorem 19.15: if a boundary-zero function takes a positive value, then on the
finite complement `Aᶜ` it attains a positive global maximum outside `A`. -/
private lemma existsPositiveGlobalMaximumOutside_of_boundaryZero
    {A : Set E} {f : E → ℝ} (hA_finite : Aᶜ.Finite) (hzero : Set.EqOn f 0 A)
    (hpos : ∃ x, 0 < f x) :
    ∃ x₀, x₀ ∉ A ∧ 0 < f x₀ ∧ IsGreatest (Set.range f) (f x₀) := by
  classical
  rcases hpos with ⟨x, hxpos⟩
  have hxA : x ∉ A := by
    intro hxA
    have hxzero : f x = 0 := hzero hxA
    linarith
  let s : Finset E := hA_finite.toFinset
  have hs_nonempty : s.Nonempty := ⟨x, by simpa [s] using hxA⟩
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := Finset.exists_max_image s f hs_nonempty
  have hx₀A : x₀ ∉ A := by
    simpa [s] using hx₀mem
  have hx₀max' : ∀ z, z ∉ A → f z ≤ f x₀ := by
    intro z hz
    exact hx₀max z (by simpa [s] using hz)
  have hx₀pos : 0 < f x₀ := by
    have hle : f x ≤ f x₀ := hx₀max' x hxA
    linarith
  refine ⟨x₀, hx₀A, hx₀pos, ?_⟩
  refine ⟨⟨x₀, rfl⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  by_cases hzA : z ∈ A
  · have hzzero : f z = 0 := hzero hzA
    linarith
  · exact hx₀max' z hzA

/-- Helper for Theorem 19.15: on a finite irreducible kernel, a harmonic function that vanishes on
`A` cannot take a positive value. -/
private lemma harmonicOutside_nonpos_of_boundaryZero_of_irreducible
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)]
    {A : Set E} {f : E → ℝ} (hA_nonempty : A.Nonempty)
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f)
    (hzero : Set.EqOn f 0 A) :
    ∀ x, f x ≤ 0 := by
  classical
  intro x
  by_contra hx
  have hxpos : 0 < f x := lt_of_not_ge hx
  obtain ⟨x₀, hx₀A, hx₀pos, hx₀max⟩ :=
    existsPositiveGlobalMaximumOutside_of_boundaryZero (A := A) (Set.toFinite Aᶜ) hzero ⟨x, hxpos⟩
  let S : Set E := {z | f z = f x₀}
  have hx₀S : x₀ ∈ S := by
    simp [S]
  have hmax : ∀ z, f z ≤ f x₀ := by
    intro z
    exact hx₀max.2 ⟨z, rfl⟩
  have hstep :
      ∀ ⦃a b : E⦄, a ∈ S → 0 < (discreteMatrixKernel p) a ({b} : Set E) → b ∈ S := by
    intro a b ha hab
    have haA : a ∉ A := by
      intro ha_mem
      have hzero_a : f a = 0 := hzero ha_mem
      have hx₀zero : f x₀ = 0 := by
        exact ha.symm.trans hzero_a
      linarith
    have hmax_at_a : ∀ z, f z ≤ f a := by
      intro z
      rw [ha]
      exact hmax z
    have hab_eq : f b = f a :=
      value_eq_of_positiveTransition_from_globalMaximum
        (p := p) (C := C) hf haA hmax_at_a hab
    show f b = f x₀
    exact hab_eq.trans ha
  obtain ⟨a, haA⟩ := hA_nonempty
  have hsingleton_pos : 0 < (Measure.count : Measure E) ({a} : Set E) := by
    simp
  rcases (inferInstance :
      Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)).irreducible
      (A := ({a} : Set E)) (MeasurableSet.singleton a) hsingleton_pos x₀ with ⟨n, hn⟩
  have haS : a ∈ S :=
    mem_maxSet_of_powSingletonMass_pos_of_stepClosed (p := p) hx₀S hstep hn
  have hzero_a : f a = 0 := hzero haA
  have hx₀zero : f x₀ = 0 := by
    exact haS.symm.trans hzero_a
  linarith

/-- Helper for Theorem 19.15: on a finite irreducible kernel, a harmonic function with boundary
value `0` on `A` vanishes identically. -/
private lemma harmonicOutside_eq_zero_of_boundaryZero_of_irreducible
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)]
    {A : Set E} {f : E → ℝ} (hA_nonempty : A.Nonempty)
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f)
    (hzero : Set.EqOn f 0 A) :
    f = 0 := by
  have hnonpos :
      ∀ x, f x ≤ 0 :=
    harmonicOutside_nonpos_of_boundaryZero_of_irreducible
      (p := p) (C := C) hA_nonempty hf hzero
  have hzero_harm :
      IsHarmonicOutside (discreteMatrixKernel p) A (fun _ : E ↦ (0 : ℝ)) := by
    let hWalk : IsRandomWalkWithWeights p C := inferInstance
    intro x hx
    letI : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel p hWalk.isStochastic
    refine ⟨Integrable.of_finite, ?_⟩
    rw [integral_zero]
  have hneg_harm : IsHarmonicOutside (discreteMatrixKernel p) A (-f) := by
    -- Proof comment: harmonicity is closed under linear combinations, so we also apply the
    -- nonpositive maximum principle to `-f`.
    simpa [Pi.smul_apply, Pi.add_apply, zero_smul, neg_one_smul] using
      IsHarmonicOutside.smul_add hf hzero_harm (-1) 0
  have hneg_zero : Set.EqOn (-f) 0 A := by
    intro x hx
    simp [hzero hx]
  have hneg_nonpos :
      ∀ x, (-f) x ≤ 0 :=
    harmonicOutside_nonpos_of_boundaryZero_of_irreducible
      (p := p) (C := C) hA_nonempty hneg_harm hneg_zero
  funext x
  exact le_antisymm (hnonpos x) (neg_nonpos.mp (by simpa using hneg_nonpos x))

/-- An electrical potential on `(E,C)` outside `A` is a potential whose Ohm-law current is a flow
on `E \ A`. -/
def IsElectricalPotential (C : E → E → ℝ≥0∞) (A : Set E) (u : E → ℝ) : Prop :=
  IsFlowOutside A (electricalCurrent C u)

-- Proof sketch: unfold `IsElectricalPotential`; the definition says exactly that the Ohm-law
-- current associated with `u` is a flow outside `A`.
/-- A function is an electrical potential exactly when its induced current is a flow on `E \ A`. -/
theorem isElectricalPotential_iff (C : E → E → ℝ≥0∞) (A : Set E) (u : E → ℝ) :
    IsElectricalPotential C A u ↔ IsFlowOutside A (electricalCurrent C u) := Iff.rfl

end

section MeasurableBridge

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]

section

variable [Fintype E]

-- Proof sketch: combine Ohm's law with Kirchhoff's rule for the induced current. After dividing
-- the identity `∑ y, C(x,y) * (u x - u y) = 0` by the total conductance `conductance C x`, the
-- remaining equality is exactly the one-step averaging equation for the random walk with weights
-- `C`.
/-- The harmonicity part of Theorem 19.15: an electrical potential on the finite conductance
network `(E,C)` is harmonic outside `A` for the random walk with transition matrix
`p(x,y) = C(x,y) / conductance C x`. -/
theorem electricalPotential_isHarmonicOn_compl
    {p C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    {A : Set E} {u : E → ℝ} (hu : IsElectricalPotential C A u) :
    IsHarmonicOutside (discreteMatrixKernel p) A u := by
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  intro x hx
  letI : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel p hWalk.isStochastic
  have h_integrable : Integrable u ((discreteMatrixKernel p) x) := Integrable.of_finite
  refine ⟨h_integrable, ?_⟩
  have hsum :
      Summable (fun z : E ↦ (p x z).toReal * ‖u z‖) := Summable.of_finite
  -- Proof comment: identify the kernel integral with the rowwise series, then use Kirchhoff's
  -- weighted-average identity at `x`.
  rw [integral_discreteMatrixKernel_eq_tsum p hWalk.isStochastic u x hsum]
  simpa [tsum_fintype] using
    (electricalPotential_average_eq (p := p) (C := C)
      (show IsFlowOutside A (electricalCurrent C u) from hu) hx)

-- Proof sketch: apply `electricalPotential_isHarmonicOn_compl` to both potentials and then invoke
-- the finite-state uniqueness principle for harmonic functions on `Aᶜ`. Since the electrical
-- network is finite, the complement `Aᶜ` is automatically finite, and irreducibility forces two
-- harmonic functions with the same boundary values to coincide.
/-- Theorem 19.15: if the conductance network is irreducible, an electrical potential is uniquely
determined by its boundary values on `A`. -/
theorem electricalPotential_eq_of_eqOn_boundary_of_irreducible
    {p C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)]
    {A : Set E} (hA_nonempty : A.Nonempty) {u v : E → ℝ}
    (hu : IsElectricalPotential C A u) (hv : IsElectricalPotential C A v)
    (h_eq : Set.EqOn u v A) :
    u = v := by
  have hu_harm :
      IsHarmonicOutside (discreteMatrixKernel p) A u :=
    electricalPotential_isHarmonicOn_compl (p := p) (C := C) hu
  have hv_harm :
      IsHarmonicOutside (discreteMatrixKernel p) A v :=
    electricalPotential_isHarmonicOn_compl (p := p) (C := C) hv
  have hdiff_harm :
      IsHarmonicOutside (discreteMatrixKernel p) A (u - v) := by
    -- Proof comment: the difference of two harmonic potentials is again harmonic on `Aᶜ`.
    simpa [sub_eq_add_neg, Pi.add_apply, Pi.smul_apply, one_smul, neg_one_smul] using
      IsHarmonicOutside.smul_add hu_harm hv_harm 1 (-1)
  have hdiff_zero : Set.EqOn (u - v) 0 A := by
    intro x hx
    simp [h_eq hx]
  have hdiff_eq_zero : u - v = 0 :=
    harmonicOutside_eq_zero_of_boundaryZero_of_irreducible
      (p := p) (C := C) hA_nonempty hdiff_harm hdiff_zero
  ext x
  have hx_zero : u x - v x = 0 := congrArg (fun f : E → ℝ ↦ f x) hdiff_eq_zero
  exact sub_eq_zero.mp hx_zero

end

end MeasurableBridge

end ProbabilityTheory
