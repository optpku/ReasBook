/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_5
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
variable {A : Set E}

include p in
/-- Helper for Theorem 19.7: irreducibility forces the discrete state space `E` to be countable. -/
private theorem countable_of_isIrreducibleMarkovChain
    (hirr : IsIrreducibleMarkovChain P X) :
    Countable E := by
  classical
  by_cases hE : IsEmpty E
  · letI := hE
    infer_instance
  · letI : Nonempty E := not_isEmpty_iff.mp hE
    let x₀ : E := Classical.choice ‹Nonempty E›
    let reachable : ℕ → Set E :=
      fun n ↦ {y : E | 0 < ((discreteMatrixKernel p ^ n) x₀) ({y} : Set E)}
    have hreachable_countable : ∀ n : ℕ, (reachable n).Countable := by
      intro n
      let μ : Measure E := ((discreteMatrixKernel p ^ n) x₀)
      let hReal : IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
      letI : IsMarkovKernel (discreteMatrixKernel p ^ n) := hReal.semigroup.isMarkovKernel n
      letI : IsProbabilityMeasure μ := inferInstance
      have hμ_countable : {y : E | 0 < μ ({y} : Set E)}.Countable := by
        simpa [μ] using
          (Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
            (As_mble := fun y : E ↦ MeasurableSet.singleton y)
            (As_disj := fun y z hyz ↦ Set.disjoint_singleton.2 hyz))
      simpa [reachable, μ] using hμ_countable
    have hcover : (⋃ n : ℕ, reachable n) = Set.univ := by
      ext y
      constructor
      · intro _
        simp
      · intro _
        let hReal : IsMarkovProcessRealization
            (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
        let hproc : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
        have hgreen : 0 < (G[P, X; 1]) x₀ y := by
          exact (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc x₀ y).2
            (hirr x₀ y)
        rcases existsPosStepMass_of_greenFunctionFrom_one_pos
            (κ := fun n ↦ discreteMatrixKernel p ^ n) P X hgreen with ⟨n, _, hmass⟩
        exact Set.mem_iUnion.2 ⟨n, by simpa [reachable] using hmass⟩
    have huniv_countable : (Set.univ : Set E).Countable := by
      simpa [hcover] using Set.countable_iUnion hreachable_countable
    exact Set.countable_univ_iff.mp huniv_countable

/-- Helper for Theorem 19.7: a finite entrance time into `A` forces the stopped value to lie in
`A`. -/
private theorem stoppedValue_mem_of_hittingAfter_lt_top
    {Ω' : Type*} [MeasurableSpace Ω'] (Y : ℕ → Ω' → E) (B : Set E) (n : ℕ)
    {ω : Ω'} (hτ : hittingAfter Y B n ω < ⊤) :
    stoppedValue Y (hittingAfter Y B n) ω ∈ B := by
  -- Proof comment: once the hitting time is finite, `stoppedValue` is evaluated at a genuine hit.
  simpa [stoppedValue] using
    hittingAfter_mem_set_of_ne_top (u := Y) (s := B) (n := n) (ω := ω) hτ.ne

include p in
/-- Helper for Theorem 19.7: every state belongs to its own first-hit positivity set `S_A x`. -/
private theorem self_mem_S_A_of_realization {x : E} :
    x ∈ S_A P X A x := by
  -- Proof comment: the first hit of `insert x A` occurs immediately at time `0` with value `x`.
  have hstart_one : (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = 1 := by
    have hmap : (P x : Measure Ω).map (X 0) = Measure.dirac x := by
      simpa using (inferInstance : IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).initial_eq x
    calc
      (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E))
          = ((P x : Measure Ω).map (X 0)) ({x} : Set E) := by
              simpa using
                (Measure.map_apply
                  ((inferInstance : IsMarkovProcessRealization
                    (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process 0)
                  (measurableSet_singleton x)).symm
      _ = 1 := by simp [hmap]
  let hitNow : Set Ω :=
    {ω | hittingAfter X (insert x A) 0 ω < ⊤ ∧
        stoppedValue X (hittingAfter X (insert x A) 0) ω = x}
  have hsubset : X 0 ⁻¹' ({x} : Set E) ⊆ hitNow := by
    intro ω hω
    have hx0 : X 0 ω = x := by simpa using hω
    have hτ0 : hittingAfter X (insert x A) 0 ω = 0 := by
      refine le_antisymm ?_ (le_hittingAfter (u := X) (s := insert x A) (n := 0) ω)
      exact hittingAfter_le_of_mem (by simp) (by simp [hx0])
    constructor
    · simp [hτ0]
    · simpa [hitNow, stoppedValue, hτ0] using hω
  have hhitNow : (P x : Measure Ω) hitNow = 1 := by
    refine le_antisymm ?_ ?_
    · calc
        (P x : Measure Ω) hitNow ≤ (P x : Measure Ω) Set.univ := measure_mono (by simp)
        _ = 1 := by simp
    · calc
        1 = (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) := hstart_one.symm
        _ ≤ (P x : Measure Ω) hitNow := measure_mono hsubset
  have hreal_pos : 0 < (P x : Measure Ω).real hitNow := by
    rw [Measure.real_def, hhitNow]
    norm_num
  have hF :
      F_A P X A x x = (P x : Measure Ω).real hitNow := by
    rfl
  rw [mem_S_A_iff, hF]
  exact hreal_pos

include p in
/-- Helper for Theorem 19.7: irreducibility and a nonempty boundary force some boundary point to
belong to `S_A x` for every `x ∉ A`. -/
private theorem existsBoundaryPoint_mem_S_A_of_irreducible
    (hirr : IsIrreducibleMarkovChain P X) (hA_nonempty : A.Nonempty) {x : E}
    (_hx : x ∉ A) :
    ∃ y, y ∈ A ∧ y ∈ S_A P X A x := by
  classical
  letI : Countable E := countable_of_isIrreducibleMarkovChain (p := p) hirr
  obtain ⟨a, haA⟩ := hA_nonempty
  let hitA : Set Ω := {ω | hittingAfter X A 0 ω < ⊤}
  have hhitSingleton_ne_zero :
      (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = a} ≠ 0 := by
    intro hzero
    have hpos : 0 < (F[P, X]) x a := hirr x a
    rw [everHitsProbability_def, Measure.real_def, hzero, ENNReal.toReal_zero] at hpos
    exact lt_irrefl _ hpos
  have hsingleton_subset : {ω | ∃ n : ℕ, 0 < n ∧ X n ω = a} ⊆ hitA := by
    intro ω hω
    rcases hω with ⟨n, hn, hXa⟩
    have hle : hittingAfter X A 0 ω ≤ n := by
      refine hittingAfter_le_of_mem (by simp) ?_
      simpa [hXa] using haA
    exact lt_of_le_of_lt hle (by simp)
  have hhitA_ne_zero : (P x : Measure Ω) hitA ≠ 0 := by
    intro hzero
    have hle : (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = a} ≤ (P x : Measure Ω) hitA :=
      measure_mono hsingleton_subset
    have hzero' :
        (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = a} = 0 := by
      exact le_antisymm (by simpa [hzero] using hle) bot_le
    exact hhitSingleton_ne_zero hzero'
  let boundarySlice : A → Set Ω :=
    fun y ↦
      {ω | hittingAfter X (insert y.1 A) 0 ω < ⊤ ∧
          stoppedValue X (hittingAfter X (insert y.1 A) 0) ω = y.1}
  have hhitA_union : hitA = ⋃ y : A, boundarySlice y := by
    ext ω
    constructor
    · intro hω
      let y : A :=
        ⟨stoppedValue X (hittingAfter X A 0) ω,
          stoppedValue_mem_of_hittingAfter_lt_top X A 0 hω⟩
      refine Set.mem_iUnion.2 ⟨y, ?_⟩
      have hyStop :
          stoppedValue X (hittingAfter X (insert y.1 A) 0) ω = y.1 := by
        simp [y, Set.insert_eq_of_mem y.2]
      constructor
      · simpa [boundarySlice, Set.insert_eq_of_mem y.2] using hω
      · simpa [boundarySlice] using hyStop
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨y, hy⟩
      simpa [hitA, boundarySlice, Set.insert_eq_of_mem y.2] using hy.1
  letI : Countable A := (Set.to_countable A).to_subtype
  obtain ⟨y, hypos⟩ :=
    exists_measure_pos_of_not_measure_iUnion_null
      (μ := (P x : Measure Ω)) (s := boundarySlice) (by simpa [hhitA_union] using hhitA_ne_zero)
  have hreal_pos : 0 < (P x : Measure Ω).real (boundarySlice y) := by
    rw [Measure.real_def]
    exact ENNReal.toReal_pos hypos.ne' (measure_ne_top (P x : Measure Ω) _)
  have hF :
      F_A P X A x y.1 = (P x : Measure Ω).real (boundarySlice y) := by
    rfl
  refine ⟨y.1, y.2, ?_⟩
  rw [mem_S_A_iff, hF]
  exact hreal_pos

/-- Helper for Theorem 19.7: a boundary-zero harmonic function for `discreteMatrixKernel p`
restricts to a harmonic function for the killed chain on `Aᶜ`. -/
private theorem isHarmonicForKilledChain_of_boundaryZero
    {f : E → ℝ}
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f)
    (hzero : Set.EqOn f 0 A) :
    IsHarmonicForKilledChain p A f := by
  intro x hx
  rcases hf hx with ⟨hf_int, hf_eq⟩
  refine ⟨hf_int.restrict, ?_⟩
  -- Proof comment: boundary-zero collapses the full-step integral to the restriction on `Aᶜ`.
  calc
    f x = ∫ y, f y ∂(discreteMatrixKernel p x) := hf_eq
    _ = ∫ y in Aᶜ, f y ∂(discreteMatrixKernel p x) := by
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := discreteMatrixKernel p x) (s := Aᶜ) fun y hy ↦ hzero (by simpa using hy)
    _ = ∫ y, f y ∂((discreteMatrixKernel p x).restrict Aᶜ) := by
      rfl

/-- Helper for Theorem 19.7: a boundary-zero function with a positive value attains a positive
global maximum at some point of the finite complement `Aᶜ`. -/
private theorem existsPositiveGlobalMaximumOutside_of_boundaryZero
    {f : E → ℝ} (hA_finite : Aᶜ.Finite) (hzero : Set.EqOn f 0 A)
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

/-- Helper for Theorem 19.7: a harmonic function on `Aᶜ` that vanishes on `A` is everywhere
nonpositive. -/
private theorem harmonicOutside_nonpos_of_boundaryZero_of_irreducible
    {f : E → ℝ} (hirr : IsIrreducibleMarkovChain P X) (hA_nonempty : A.Nonempty)
    (hA_finite : Aᶜ.Finite) (hf : IsHarmonicOutside (discreteMatrixKernel p) A f)
    (hzero : Set.EqOn f 0 A) :
    ∀ x, f x ≤ 0 := by
  let hfKilled : IsHarmonicForKilledChain p A f :=
    isHarmonicForKilledChain_of_boundaryZero (p := p) (A := A) hf hzero
  intro x
  by_contra hx
  have hxpos : 0 < f x := lt_of_not_ge hx
  obtain ⟨x₀, hx₀A, hx₀pos, hx₀max⟩ :=
    existsPositiveGlobalMaximumOutside_of_boundaryZero (A := A) hA_finite hzero ⟨x, hxpos⟩
  obtain ⟨y, hyA, hyS⟩ :=
    existsBoundaryPoint_mem_S_A_of_irreducible (p := p) hirr hA_nonempty hx₀A
  have hmaxS : IsGreatest (f '' S_A P X A x₀) (f x₀) := by
    refine ⟨⟨x₀, self_mem_S_A_of_realization (p := p), rfl⟩, ?_⟩
    rintro _ ⟨z, _, rfl⟩
    exact hx₀max.2 ⟨z, rfl⟩
  have hyEq :
      f y = f x₀ := harmonicOn_compl_eq_on_S_A_of_isGreatest
        (p := p) (P := P) (X := X) (A := A) (f := f) (x₀ := x₀) hfKilled hx₀A hmaxS hyS
  have hyZero : f y = 0 := hzero hyA
  linarith

-- Proof sketch: apply Theorem 19.2 to the difference `f₁ - f₂`, which is harmonic on `Aᶜ` and
-- vanishes on `A`. If the difference were nonzero, choose a positive maximum on the finite set
-- `Aᶜ`; the source-facing irreducibility owner `IsIrreducibleMarkovChain P X` gives positive
-- first-hit probability between off-boundary states, and Theorem 19.6 then forces the maximum
-- point to share its value with some boundary point, contradicting the boundary value `0`.
/-- Theorem 19.7: for an irreducible discrete-time Markov chain realization with transition matrix
`p`, if `A` is nonempty with finite complement and two functions are harmonic on `E \ A` and
agree on `A`, then they agree everywhere. -/
theorem harmonicOn_compl_ext_of_irreducible
    {f₁ f₂ : E → ℝ}
    (hirr : IsIrreducibleMarkovChain P X)
    (hA_nonempty : A.Nonempty) (hA_finite : Aᶜ.Finite)
    (hf₁ : IsHarmonicOutside (discreteMatrixKernel p) A f₁)
    (hf₂ : IsHarmonicOutside (discreteMatrixKernel p) A f₂)
    (h_eq : Set.EqOn f₁ f₂ A) :
    f₁ = f₂ := by
  -- Proof comment: apply the nonpositive maximum principle to both differences `f₁ - f₂` and
  -- `f₂ - f₁`, then compare pointwise by `le_antisymm`.
  have hf12 : IsHarmonicOutside (discreteMatrixKernel p) A (f₁ - f₂) := by
    simpa [sub_eq_add_neg, Pi.add_apply, Pi.smul_apply, one_smul, neg_one_smul] using
      IsHarmonicOutside.smul_add hf₁ hf₂ 1 (-1)
  have hf21 : IsHarmonicOutside (discreteMatrixKernel p) A (f₂ - f₁) := by
    simpa [sub_eq_add_neg, Pi.add_apply, Pi.smul_apply, one_smul, neg_one_smul] using
      IsHarmonicOutside.smul_add hf₂ hf₁ 1 (-1)
  have h12_zero : Set.EqOn (f₁ - f₂) 0 A := by
    intro x hx
    simp [Pi.sub_apply, h_eq hx]
  have h21_zero : Set.EqOn (f₂ - f₁) 0 A := by
    intro x hx
    simp [Pi.sub_apply, h_eq hx]
  have h12_nonpos :
      ∀ x, (f₁ - f₂) x ≤ 0 :=
    harmonicOutside_nonpos_of_boundaryZero_of_irreducible
      (p := p) (P := P) (X := X) (A := A)
      hirr hA_nonempty hA_finite hf12 h12_zero
  have h21_nonpos :
      ∀ x, (f₂ - f₁) x ≤ 0 :=
    harmonicOutside_nonpos_of_boundaryZero_of_irreducible
      (p := p) (P := P) (X := X) (A := A)
      hirr hA_nonempty hA_finite hf21 h21_zero
  funext x
  exact le_antisymm (sub_nonpos.mp (h12_nonpos x)) (sub_nonpos.mp (h21_nonpos x))

-- Proof sketch: each solution of the Dirichlet problem is harmonic on `Aᶜ` and equals the same
-- boundary datum `g` on `A`, so `harmonicOn_compl_ext_of_irreducible` applies directly.
/-- Two solutions of the same Dirichlet problem for `p - I` with the same boundary data coincide
under the irreducible Markov-chain hypotheses of Theorem 19.7. -/
theorem solvesDirichletProblem_unique
    {g f₁ f₂ : E → ℝ}
    (hirr : IsIrreducibleMarkovChain P X)
    (hA_nonempty : A.Nonempty) (hA_finite : Aᶜ.Finite)
    (hf₁ : SolvesDirichletProblem (discreteMatrixKernel p) A g f₁)
    (hf₂ : SolvesDirichletProblem (discreteMatrixKernel p) A g f₂) :
    f₁ = f₂ := by
  -- Proof comment: the two Dirichlet solutions share the same harmonicity data and the same
  -- boundary values, so Theorem 19.7 applies directly.
  rcases (solvesDirichletProblem_iff (discreteMatrixKernel p) A g f₁).1 hf₁ with ⟨hf₁harm, hf₁eq⟩
  rcases (solvesDirichletProblem_iff (discreteMatrixKernel p) A g f₂).1 hf₂ with ⟨hf₂harm, hf₂eq⟩
  apply harmonicOn_compl_ext_of_irreducible
    (p := p) (P := P) (X := X) (A := A) hirr hA_nonempty hA_finite hf₁harm hf₂harm
  intro x hx
  exact (hf₁eq hx).trans (hf₂eq hx).symm

end

end ProbabilityTheory
