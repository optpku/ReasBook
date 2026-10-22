/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_41
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_42
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

noncomputable section

namespace ProbabilityTheory

/-- Helper for Remark 17.4: the time-`t` state kernel induced by a path-space kernel on `I → E`. -/
abbrev transitionKernel {I : Type u} {E : Type v} [MeasurableSpace E]
    (κ : Kernel E (I → E)) (t : I) : Kernel E E :=
  κ.map fun y ↦ y t

/-- Helper for Remark 17.4: evaluating `transitionKernel κ t` at `x` is the pushforward of the
path law `κ x` by the time-`t` coordinate projection. -/
theorem transitionKernel_apply {I : Type u} {E : Type v} [MeasurableSpace E]
    (κ : Kernel E (I → E)) (t : I) (x : E) :
    transitionKernel κ t x = (κ x).map (fun y ↦ y t) := by
  -- Proof comment: `transitionKernel` is just `Kernel.map` along evaluation at time `t`.
  simpa [transitionKernel] using Kernel.map_apply κ (measurable_pi_apply t) x

end ProbabilityTheory

section

variable {E : Type u} [MeasurableSpace E] [StandardBorelSpace E]
variable (I : AddSubmonoid NNReal) (κt : I → Kernel E E) [IsMarkovSemigroup κt]
variable (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I)

omit [StandardBorelSpace E] in
/-- Helper for Remark 17.4: the ordered-difference family cut out from the semigroup `κt`
satisfies the consistency relation required by Theorem 14.42. -/
lemma orderedDifferenceFamilyConsistent :
    IsConsistentKernelFamily
      (fun {s t : I} hst ↦ κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩) := by
  let hκ : IsMarkovSemigroup κt := inferInstance
  intro r s t hrs hst
  let rs : I := ⟨s.1 - r.1, hsub hrs.le⟩
  let st : I := ⟨t.1 - s.1, hsub hst.le⟩
  let rt : I := ⟨t.1 - r.1, hsub (hrs.le.trans hst.le)⟩
  have hsum : rs + st = rt := by
    apply Subtype.ext
    change s.1 - r.1 + (t.1 - s.1) = t.1 - r.1
    rw [add_comm]
    exact tsub_add_tsub_cancel
      (show s.1 ≤ t.1 from hst.le)
      (show r.1 ≤ s.1 from hrs.le)
  -- Proof comment: Chapman--Kolmogorov for the two consecutive time gaps collapses to the direct
  -- gap `t - r` after identifying the sum of the NNReal differences.
  have hcomp : κt st ∘ₖ κt rs = κt rt := by
    calc
      κt st ∘ₖ κt rs = κt (rs + st) := hκ.comp_eq rs st
      _ = κt rt := by rw [hsum]
  simpa [rs, st, rt] using hcomp

omit [IsMarkovSemigroup κt] in
/-- Helper for Remark 17.4: the finite-dimensional marginal at the singleton chain `j₀ = 0`
forces the derived transition kernel at time `0` to be `Kernel.id`. -/
lemma transitionKernel_zero_eq_id_ofPathMarginals
    (κ : Kernel E (I → E))
    (hκ :
      ∀ (x : E) {n : ℕ} (j : Π _ : Finset.Iic n, I), ∀ hj : StrictMono j,
        j ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩ = 0 →
          (κ x).map (finiteCoordinateProjection j) =
            consistentFamilyFiniteDimensionalKernel
              (fun {s t : I} hst ↦
                κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩)
              j hj x) :
    transitionKernel κ 0 = Kernel.id := by
  ext x s hs
  let j : Π _ : Finset.Iic 0, I := fun _ ↦ 0
  let e : (Π _ : Finset.Iic 0, E) ≃ᵐ E :=
    MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ E)
  have hj : StrictMono j := Subsingleton.strictMono _
  have hmap :
      ((κ x).map (finiteCoordinateProjection j)).map e =
        (consistentFamilyFiniteDimensionalKernel
          (fun {s t : I} hst ↦ κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩)
          j hj x).map e := by
    exact congrArg (fun μ : Measure (Π _ : Finset.Iic 0, E) => μ.map e) (hκ x j hj rfl)
  have hmap' : (((κ x).map (finiteCoordinateProjection j)).map e) s =
      ((consistentFamilyFiniteDimensionalKernel
        (fun {s t : I} hst ↦ κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩)
        j hj x).map e) s := by
    exact congrArg (fun μ : Measure E ↦ μ s) hmap
  have heval :
      e ∘ finiteCoordinateProjection j = fun ω : I → E ↦ ω 0 := by
    funext ω
    simp [j, e, finiteCoordinateProjection]
  have heMeasurable : Measurable e := by
    fun_prop
  have hleft :
      transitionKernel κ 0 x s = (((κ x).map (finiteCoordinateProjection j)).map e) s := by
    rw [transitionKernel_apply]
    rw [Measure.map_map heMeasurable (measurable_finiteCoordinateProjection j), heval]
  have hright :
      ((consistentFamilyFiniteDimensionalKernel
          (fun {s t : I} hst ↦ κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩)
          j hj x).map e) s = s.indicator 1 x := by
    rw [consistentFamilyFiniteDimensionalKernel_apply]
    simp [j, e, consistentFamilyFiniteDimensionalMeasure_zero, hs]
  -- Transport the one-point finite-dimensional law through the unique-coordinate equivalence.
  calc
    transitionKernel κ 0 x s = (((κ x).map (finiteCoordinateProjection j)).map e) s := hleft
    _ = ((consistentFamilyFiniteDimensionalKernel
        (fun {s t : I} hst ↦ κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩)
        j hj x).map e) s := hmap'
    _ = s.indicator 1 x := hright
    _ = (Kernel.id x) s := by
      by_cases hx : x ∈ s <;> simp [Kernel.id_apply, hs, hx]

/-- Helper for Remark 17.4: the canonical two-point chain starts at `0` and ends at `t`. -/
def twoPointChain (t : I) : Π _ : Finset.Iic 1, I :=
  fun k ↦ if k.1 = 0 then 0 else t

/-- Helper for Remark 17.4: the first point of `twoPointChain t` is `0`. -/
lemma twoPointChain_zero (t : I) :
    twoPointChain (I := I) t ⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ = 0 := by
  simp [twoPointChain]

/-- Helper for Remark 17.4: the second point of `twoPointChain t` is `t`. -/
lemma twoPointChain_one (t : I) :
    twoPointChain (I := I) t ⟨1, Finset.mem_Iic.2 le_rfl⟩ = t := by
  simp [twoPointChain]

/-- Helper for Remark 17.4: if `0 < t`, then the chain `0 < t` is strictly increasing. -/
lemma twoPointChain_strictMono {t : I} (ht : 0 < t) :
    StrictMono (twoPointChain (I := I) t) := by
  intro a b hab
  have hab' : a.1 < b.1 := hab
  have ha_le : a.1 ≤ 1 := Finset.mem_Iic.mp a.2
  have hb_le : b.1 ≤ 1 := Finset.mem_Iic.mp b.2
  have ha : a.1 = 0 := by
    omega
  have hb : b.1 = 1 := by
    omega
  simpa [twoPointChain, ha, hb] using ht

omit [MeasurableSpace E] [StandardBorelSpace E] in
/-- Helper for Remark 17.4: the last coordinate of the two-point finite projection is evaluation
at time `t`. -/
lemma finiteCoordinateProjection_twoPoint_last (t : I) :
    (fun ω : I → E ↦ (finiteCoordinateProjection (twoPointChain (I := I) t) ω)
      ⟨1, Finset.mem_Iic.2 le_rfl⟩) = fun ω : I → E ↦ ω t := by
  funext ω
  simp [finiteCoordinateProjection, twoPointChain]

omit [StandardBorelSpace E] in
/-- Helper for Remark 17.4: for the two-point chain `(0, t)`, the last-coordinate pushforward of
the canonical finite-dimensional kernel is exactly `κt t`. -/
lemma twoPointFiniteDimensionalKernel_map_last
    (t : I) (ht : 0 < t) :
    (consistentFamilyFiniteDimensionalKernel
        (fun {s t : I} hst ↦ κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩)
        (twoPointChain (I := I) t)
        (twoPointChain_strictMono (I := I) ht)).map
        (fun z : Π _ : Finset.Iic 1, E ↦ z ⟨1, Finset.mem_Iic.2 le_rfl⟩) =
      κt t := by
  let K : ∀ ⦃s t : I⦄, s < t → Kernel E E :=
    fun {s t} hst ↦ κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩
  let j : Π _ : Finset.Iic 1, I := twoPointChain (I := I) t
  let hj : StrictMono j := twoPointChain_strictMono (I := I) ht
  let last : (Π _ : Finset.Iic 1, E) → E := fun z ↦ z ⟨1, Finset.mem_Iic.2 le_rfl⟩
  let initialHistory : E → Π _ : Finset.Iic 0, E := fun x _ ↦ x
  let singletonHistory : (Π _ : Finset.Iic 0, E) → E :=
    fun z ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le 0)⟩
  let κhist : (m : ℕ) → Kernel (Π _ : Finset.Iic m, E) E :=
    fun m ↦
      if hm : m < 1 then
        Kernel.comap
          (K (hj (show
            (⟨m, Finset.mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic 1) <
              ⟨m + 1, Finset.mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)))
          (fun z ↦ z ⟨m, Finset.mem_Iic.2 le_rfl⟩)
          (measurable_pi_apply ((⟨m, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic m)))
      else
        Kernel.deterministic
          (fun z ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩)
          (measurable_pi_apply ((⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩ : Finset.Iic m)))
  have hInitialHistoryMeasurable : Measurable initialHistory := by
    fun_prop
  have hSingletonHistoryMeasurable : Measurable singletonHistory := by
    simpa [singletonHistory] using
      measurable_pi_apply ((⟨0, Finset.mem_Iic.2 (Nat.zero_le 0)⟩ : Finset.Iic 0))
  have h01 :
      j ⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ <
        j ⟨1, Finset.mem_Iic.2 le_rfl⟩ := by
    exact hj (show
      (⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ : Finset.Iic 1) <
        ⟨1, Finset.mem_Iic.2 le_rfl⟩ from Nat.lt_succ_self 0)
  have hKernelDef :
      consistentFamilyFiniteDimensionalKernel K j hj =
        (((@ProbabilityTheory.Kernel.partialTraj (fun _ : ℕ ↦ E) _ κhist 0 1) :
            Kernel (Π _ : Finset.Iic 0, E) (Π _ : Finset.Iic 1, E)) ∘ₖ
          Kernel.deterministic initialHistory hInitialHistoryMeasurable) := by
    rfl
  -- Proof comment: the two-point ordered history is a single transition from the singleton
  -- initial history, so pushing to the last coordinate recovers the one-step kernel `κt t`.
  rw [hKernelDef, Kernel.map_comp]
  have hκhistZero :
      κhist 0 = Kernel.comap (K h01) singletonHistory hSingletonHistoryMeasurable := by
    simp [κhist, singletonHistory]
  have htraj :
      (((@ProbabilityTheory.Kernel.partialTraj (fun _ : ℕ ↦ E) _ κhist 0 1) :
          Kernel (Π _ : Finset.Iic 0, E) (Π _ : Finset.Iic 1, E)).map last) =
        Kernel.comap (K h01) singletonHistory hSingletonHistoryMeasurable := by
    letI : ∀ n, IsMarkovKernel (κhist n) := by
      intro n
      by_cases hn : n < 1
      · dsimp [κhist]
        rw [dif_pos hn]
        infer_instance
      · dsimp [κhist]
        rw [dif_neg hn]
        infer_instance
    rw [ProbabilityTheory.Kernel.map_partialTraj_succ_self]
    simpa [last] using hκhistZero
  rw [htraj]
  rw [Kernel.comp_deterministic_eq_comap]
  rw [← Kernel.comap_comp_right
    (κ := K h01) (f := initialHistory) (g := singletonHistory)
    (hf := hInitialHistoryMeasurable) (hg := hSingletonHistoryMeasurable)]
  -- Proof comment: on the singleton initial history, the terminal coordinate is the starting
  -- state itself, so the comap collapses to the identity.
  have hId : singletonHistory ∘ initialHistory = id := by
    funext x
    rfl
  have hCollapse :
      Kernel.comap (K h01) (singletonHistory ∘ initialHistory)
        (hSingletonHistoryMeasurable.comp hInitialHistoryMeasurable) = K h01 := by
    ext x s hs
    simp [hId]
  have hKt : K h01 = κt t := by
    apply congrArg κt
    apply Subtype.ext
    simp [j, twoPointChain]
  exact hCollapse.trans hKt

omit [StandardBorelSpace E] in
/-- Helper for Remark 17.4: the two-point finite-dimensional marginal identifies the derived
transition kernel at time `t > 0` with the prescribed kernel `κt t`. -/
lemma transitionKernel_eq_ofTwoPointMarginals
    (κ : Kernel E (I → E))
    (hκ :
      ∀ (x : E) {n : ℕ} (j : Π _ : Finset.Iic n, I), ∀ hj : StrictMono j,
        j ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩ = 0 →
          (κ x).map (finiteCoordinateProjection j) =
            consistentFamilyFiniteDimensionalKernel
              (fun {s t : I} hst ↦
                κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩)
              j hj x)
    (t : I) (ht : 0 < t) :
    transitionKernel κ t = κt t := by
  let K : ∀ ⦃s t : I⦄, s < t → Kernel E E :=
    fun {s t} hst ↦ κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩
  let j : Π _ : Finset.Iic 1, I := twoPointChain (I := I) t
  let hj : StrictMono j := twoPointChain_strictMono (I := I) ht
  let last : (Π _ : Finset.Iic 1, E) → E := fun z ↦ z ⟨1, Finset.mem_Iic.2 le_rfl⟩
  have hstart : j ⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ = 0 := by
    simpa [j] using twoPointChain_zero (I := I) t
  have hmarg :
      ∀ x, (κ x).map (finiteCoordinateProjection j) =
        consistentFamilyFiniteDimensionalKernel K j hj x := by
    intro x
    simpa [K] using hκ x j hj hstart
  have h01idx :
      (⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ : Finset.Iic 1) <
        ⟨1, Finset.mem_Iic.2 le_rfl⟩ := by
    decide
  have h01 :
      j ⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ <
        j ⟨1, Finset.mem_Iic.2 le_rfl⟩ := hj h01idx
  have hkernel :
      (consistentFamilyFiniteDimensionalKernel K j hj).map last = κt t := by
    simpa [K, j, hj, last] using
      (twoPointFiniteDimensionalKernel_map_last
        (I := I) (κt := κt) (hsub := hsub) t ht)
  ext x s hs
  have hmap :
      ((κ x).map (finiteCoordinateProjection j)).map last =
        (consistentFamilyFiniteDimensionalKernel K j hj x).map last := by
    exact congrArg (fun μ : Measure (Π _ : Finset.Iic 1, E) => μ.map last) (hmarg x)
  have hleft :
      transitionKernel κ t x s = (((κ x).map (finiteCoordinateProjection j)).map last) s := by
    -- Proof comment: the last coordinate of the two-point projection is evaluation at time `t`.
    have hlastMeasurable : Measurable last := by
      fun_prop
    have hlastEval :
        last ∘ finiteCoordinateProjection j = fun ω : I → E ↦ ω t := by
      funext ω
      simpa [j, last] using
        congrFun (finiteCoordinateProjection_twoPoint_last (I := I) (E := E) t) ω
    rw [transitionKernel_apply, Measure.map_map hlastMeasurable
      (measurable_finiteCoordinateProjection j), hlastEval]
  have hright :
      ((consistentFamilyFiniteDimensionalKernel K j hj x).map last) s = κt t x s := by
    have hkernelEval :
        ((consistentFamilyFiniteDimensionalKernel K j hj).map last) x = (κt t) x := by
      exact congrArg (fun η : Kernel E E => η x) hkernel
    have hlastMeasurable : Measurable last := by
      fun_prop
    simpa [Kernel.map_apply, hlastMeasurable] using
      congrArg (fun μ : Measure E ↦ μ s) hkernelEval
  calc
    transitionKernel κ t x s = (((κ x).map (finiteCoordinateProjection j)).map last) s := hleft
    _ = ((consistentFamilyFiniteDimensionalKernel K j hj x).map last) s := by
      rw [hmap]
    _ = κt t x s := by
      rw [hright]

/-- Helper for Remark 17.4: a nonzero time in an additive submonoid of `NNReal` is positive. -/
lemma submonoidTime_pos_of_ne_zero (t : I) (ht : t ≠ 0) :
    0 < t := by
  -- Proof comment: an `NNReal` coordinate is positive exactly when it is not zero.
  have ht0 : (0 : NNReal) < t.1 := pos_iff_ne_zero.mpr fun h0 ↦
    ht (Subtype.ext (by simpa using h0))
  simpa using ht0

-- Proof sketch: use the ordered-difference closure of `I` to turn the semigroup `κt` into the
-- consistent two-time family `(s, t) ↦ κ_{t - s}` on the time set `I`, then apply the Chapter 14
-- path-kernel existence theorem to obtain a path-space kernel with the canonical
-- finite-dimensional marginals.
/-- Remark 17.4: if the additive time set `I ⊆ [0, ∞)` is closed under ordered differences, then
a time-homogeneous family of transition probabilities on `I` already determines a stochastic
kernel on the full path space `E^I`. Thus the kernel `κ` from Definition 17.3 is forced, at the
level of finite-dimensional marginals, by the transition kernels `κ_t`. -/
theorem exists_pathKernel_of_timeHomogeneousTransitionKernels
    :
    ∃ κ : Kernel E (I → E),
      IsMarkovKernel κ ∧
        ∀ (x : E) {n : ℕ} (j : Π _ : Finset.Iic n, I), ∀ hj : StrictMono j,
          j ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩ = 0 →
            (κ x).map (finiteCoordinateProjection j) =
              consistentFamilyFiniteDimensionalKernel
                (fun {s t : I} hst ↦
                  κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩)
                j hj x := by
  let K : ∀ ⦃s t : I⦄, s < t → Kernel E E :=
    fun {s t} hst ↦ κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩
  have hMarkov : ∀ {s t : I} (hst : s < t), IsMarkovKernel (K hst) := by
    intro s t hst
    infer_instance
  have hConsistent : IsConsistentKernelFamily K := by
    -- The ordered-difference family is exactly the consistent family from the helper lemma.
    simpa [K] using
      (orderedDifferenceFamilyConsistent (I := I) (κt := κt) (hsub := hsub))
  -- Apply Theorem 14.42 on the subtype time set underlying the additive submonoid `I`.
  simpa [K] using
    (exists_kernel_on_path_space_of_consistent_family
      (E := E) (I := (I : Set NNReal)) (h0I := I.zero_mem) K hMarkov hConsistent)

-- Proof sketch: apply the finite-dimensional marginal statement to the two-time chain `(0, t)` and
-- rewrite the resulting pushforward identity in terms of `transitionKernel`.
/-- The one-time transition kernels are a derived consequence of the finite-dimensional path-kernel
realization from Remark 17.4. -/
theorem exists_pathKernel_with_transitionKernel_of_timeHomogeneousTransitionKernels
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I)
    :
    ∃ κ : Kernel E (I → E),
      IsMarkovKernel κ ∧
        ∀ t : I, transitionKernel κ t = κt t := by
  rcases exists_pathKernel_of_timeHomogeneousTransitionKernels
      (I := I) (κt := κt) (hsub := hsub) with ⟨κ, hMarkov, hκ⟩
  refine ⟨κ, hMarkov, ?_⟩
  intro t
  by_cases ht : t = 0
  · -- The singleton-time marginal fixes the time-zero transition.
    simpa [ht, IsMarkovSemigroup.zero_eq (κ := κt)] using
      transitionKernel_zero_eq_id_ofPathMarginals
        (I := I) (κt := κt) (hsub := hsub) κ hκ
  · -- The positive-time case is reduced to the two-point marginal helper.
    have ht0 : 0 < t := submonoidTime_pos_of_ne_zero (I := I) t ht
    simpa using
      transitionKernel_eq_ofTwoPointMarginals
        (I := I) (κt := κt) (hsub := hsub) κ hκ t ht0

end
