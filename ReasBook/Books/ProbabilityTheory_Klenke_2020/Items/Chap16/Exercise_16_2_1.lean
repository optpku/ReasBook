/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_4_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_20
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure
open Filter
open scoped Topology ComplexConjugate

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- Source-facing strict `α`-stability for real probability laws. Unlike the chapter owner
`IsStableWithIndex`, this predicate keeps the textbook positivity and scaling law visible without
baking in the later conclusion that `α ≤ 2`. -/
def IsStrictlyStableWithIndex (μ : ProbabilityMeasure ℝ) (α : ℝ) : Prop :=
  0 < α ∧
    (∀ x : ℝ, μ ≠ diracProba x) ∧
      ∀ n : ℕ+,
        μ ^ (n : ℕ) =
          map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) 0).aemeasurable

/-- Source-facing broad `α`-stability for real probability laws. This keeps the centering data in
the public interface while deferring only the later upper bound `α ≤ 2` to a bridge lemma. -/
def IsBroadlyStableWithIndex (μ : ProbabilityMeasure ℝ) (α : ℝ) : Prop :=
  0 < α ∧
    (∀ x : ℝ, μ ≠ diracProba x) ∧
      ∃ d : ℕ+ → ℝ,
        ∀ n : ℕ+,
          μ ^ (n : ℕ) =
            map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) (d n)).aemeasurable

variable {μ : ProbabilityMeasure ℝ} {α : ℝ}

namespace IsStrictlyStableWithIndex

/-- On the admissible index range, the source-facing strict `α`-stability predicate specializes to
the chapter owner abstraction `IsStableWithIndex`. -/
theorem toIsStableWithIndex
    (hμ : IsStrictlyStableWithIndex μ α) (hα : α ≤ 2) :
    IsStableWithIndex μ α :=
  ⟨hμ.2.1, ⟨hμ.1, hα⟩, hμ.2.2⟩

end IsStrictlyStableWithIndex

namespace IsBroadlyStableWithIndex

/-- On the admissible index range, the source-facing broad `α`-stability predicate specializes to
the chapter owner abstraction `IsStableInBroadSenseWithIndex`. -/
theorem toIsStableInBroadSenseWithIndex
    (hμ : IsBroadlyStableWithIndex μ α) (hα : α ≤ 2) :
    IsStableInBroadSenseWithIndex μ α :=
  ⟨hμ.2.1, ⟨hμ.1, hα⟩, hμ.2.2⟩

end IsBroadlyStableWithIndex

/-- Helper for Exercise 16.2.1: a continuous zero-free complex-valued function on `ℝ`
normalized by `φ 0 = 1` admits a unique continuous lift through `Complex.exp` starting at `0`.
-/
lemma existsUnique_continuousExpLift {φ : ℝ → ℂ}
    (hφcont : Continuous φ) (hφnonzero : ∀ t : ℝ, φ t ≠ 0) (hφ0 : φ 0 = 1) :
    ∃! Ψ : C(ℝ, ℂ), Ψ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ t) = φ t := by
  let f : C(ℝ, {z : ℂ // z ≠ 0}) :=
    ⟨fun t ↦ ⟨φ t, hφnonzero t⟩, hφcont.subtype_mk _⟩
  have he :
      (fun z : ℂ ↦ (⟨Complex.exp z, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) 0 = f 0 := by
    -- Proof comment: the chosen lift must start above `φ 0 = 1`.
    ext
    simp [f, hφ0]
  rcases Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0 he with
    ⟨Ψ, hΨ, hΨuniq⟩
  refine ⟨Ψ, ?_, ?_⟩
  · rcases hΨ with ⟨hΨ0, hΨexp⟩
    refine ⟨hΨ0, ?_⟩
    intro t
    -- Proof comment: after forgetting the nonzero subtype, the lifted map exponentiates back to
    -- `φ`.
    simpa [f] using congrArg Subtype.val (congr_fun hΨexp t)
  · intro Ψ' hΨ'
    apply hΨuniq
    rcases hΨ' with ⟨hΨ'0, hΨ'exp⟩
    refine ⟨hΨ'0, ?_⟩
    funext t
    -- Proof comment: uniqueness of lifts is checked in the nonzero subtype by rebuilding the
    -- covering equation pointwise.
    apply Subtype.ext
    simpa [f] using hΨ'exp t

/-- Helper for Exercise 16.2.1: the characteristic function of the `n`th convolution power is
the `n`th pointwise power of the original characteristic function. -/
lemma charFun_pow_eq_pow (ν : ProbabilityMeasure ℝ) (n : ℕ) :
    charFun ((ν ^ n : ProbabilityMeasure ℝ) : Measure ℝ) =
      fun t ↦ charFun (ν : Measure ℝ) t ^ n := by
  induction n with
  | zero =>
      -- Proof comment: the zeroth convolution power is `δ₀`, whose characteristic function is `1`.
      funext t
      simp [ProbabilityMeasure.one_eq_diracProba, MeasureTheory.diracProba]
  | succ n ih =>
      -- Proof comment: one additional convolution factor multiplies the characteristic function by
      -- one additional copy of `charFun ν`.
      funext t
      calc
        charFun ((ν ^ (n + 1) : ProbabilityMeasure ℝ) : Measure ℝ) t
            = charFun ((((ν ^ n : ProbabilityMeasure ℝ) : Measure ℝ)) ∗ (ν : Measure ℝ)) t := by
                simp [pow_succ]
        _ = charFun (((ν ^ n : ProbabilityMeasure ℝ) : Measure ℝ)) t *
              charFun (ν : Measure ℝ) t := by
              simpa using
                (MeasureTheory.charFun_conv
                  (μ := (((ν ^ n : ProbabilityMeasure ℝ) : Measure ℝ)))
                  (ν := (ν : Measure ℝ)) t)
        _ = charFun (ν : Measure ℝ) t ^ n * charFun (ν : Measure ℝ) t := by
              rw [ih]
        _ = charFun (ν : Measure ℝ) t ^ (n + 1) := by
              simp [pow_succ]

/-- Helper for Exercise 16.2.1: the source-facing strict scaling law rewrites to the usual
characteristic-function identity `φ(n^(1 / α) t) = φ(t)^n`. -/
lemma strictStable_charFunScaling
    (hμ : IsStrictlyStableWithIndex μ α) (n : ℕ+) (t : ℝ) :
    charFun (μ : Measure ℝ) (((n : ℝ) ^ (1 / α)) * t) =
      charFun (μ : Measure ℝ) t ^ (n : ℕ) := by
  -- Proof comment: evaluate the source-facing convolution-power identity at frequency `t`.
  have hchar :=
    congrArg (fun ν : ProbabilityMeasure ℝ ↦ charFun (ν : Measure ℝ) t) (hμ.2.2 n)
  calc
    charFun (μ : Measure ℝ) (((n : ℝ) ^ (1 / α)) * t)
        = charFun (Measure.map (fun x : ℝ ↦ ((n : ℝ) ^ (1 / α)) * x) (μ : Measure ℝ)) t := by
            symm
            simpa using
              (MeasureTheory.charFun_map_mul
                (μ := (μ : Measure ℝ)) (((n : ℝ) ^ (1 / α))) t)
    _ = charFun ((μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t := by
          simpa [measurable_affineMap, zero_add] using hchar.symm
    _ = charFun (μ : Measure ℝ) t ^ (n : ℕ) := by
          simp [charFun_pow_eq_pow]

/-- Helper for Exercise 16.2.1: the characteristic function of an affine image on `ℝ` is the
scaled characteristic function multiplied by the translation phase. -/
lemma charFun_map_affine
    (ν : ProbabilityMeasure ℝ) (a d t : ℝ) :
    charFun (Measure.map (fun x : ℝ ↦ a * x + d) (ν : Measure ℝ)) t =
      charFun (ν : Measure ℝ) (a * t) * Complex.exp (d * t * Complex.I) := by
  -- Proof comment: split the affine map into the scaling step and the translation step.
  calc
    charFun (Measure.map (fun x : ℝ ↦ a * x + d) (ν : Measure ℝ)) t
        = charFun (Measure.map (fun y : ℝ ↦ y + d)
            (Measure.map (fun x : ℝ ↦ a * x) (ν : Measure ℝ))) t := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · fun_prop
    _ = charFun (Measure.map (fun x : ℝ ↦ a * x) (ν : Measure ℝ)) t *
          Complex.exp (((inner ℝ d t : ℝ) : ℂ) * Complex.I) := by
            simpa using
              (MeasureTheory.charFun_map_add_const
                (μ := Measure.map (fun x : ℝ ↦ a * x) (ν : Measure ℝ)) d t)
    _ = charFun (Measure.map (fun x : ℝ ↦ a * x) (ν : Measure ℝ)) t *
          Complex.exp (d * t * Complex.I) := by
            have hinner_real : (inner ℝ d t : ℝ) = d * t := by
              simp [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]
            have hinner : ((inner ℝ d t : ℝ) : ℂ) = (d * t : ℂ) := by
              exact_mod_cast hinner_real
            rw [hinner]
    _ = charFun (ν : Measure ℝ) (a * t) * Complex.exp (d * t * Complex.I) := by
          rw [MeasureTheory.charFun_map_mul]

/-- Helper for Exercise 16.2.1: reflect a real probability law across the origin. -/
noncomputable def reflectedLaw (ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ν.map ((measurable_const.mul measurable_id).aemeasurable :
    AEMeasurable (fun x : ℝ ↦ (-1 : ℝ) * x) (ν : Measure ℝ))

/-- Helper for Exercise 16.2.1: symmetrize a real probability law by convolving it with its
reflection. -/
noncomputable def symmetrizedLaw (ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ν * reflectedLaw ν

/-- Helper for Exercise 16.2.1: reflecting a law conjugates its characteristic function. -/
lemma charFun_reflectedLaw
    (ν : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (reflectedLaw ν : Measure ℝ) t =
      conj (charFun (ν : Measure ℝ) t) := by
  -- Proof comment: reflection sends `t` to `-t`, and real characteristic functions conjugate
  -- under sign reversal.
  calc
    charFun (reflectedLaw ν : Measure ℝ) t
        = charFun (ν : Measure ℝ) ((-1 : ℝ) * t) := by
            simpa [reflectedLaw] using
              (MeasureTheory.charFun_map_mul (μ := (ν : Measure ℝ)) (-1) t)
    _ = charFun (ν : Measure ℝ) (-t) := by simp
    _ = conj (charFun (ν : Measure ℝ) t) := MeasureTheory.charFun_neg t

/-- Helper for Exercise 16.2.1: the symmetrized characteristic function is the product of the
original one with its complex conjugate. -/
lemma charFun_symmetrizedLaw
    (ν : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (symmetrizedLaw ν : Measure ℝ) t =
      charFun (ν : Measure ℝ) t * conj (charFun (ν : Measure ℝ) t) := by
  -- Proof comment: convolution multiplies characteristic functions, and the reflected factor is
  -- the conjugate one.
  calc
    charFun (symmetrizedLaw ν : Measure ℝ) t
        = charFun (ν : Measure ℝ) t * charFun (reflectedLaw ν : Measure ℝ) t := by
            simpa [symmetrizedLaw] using
              (MeasureTheory.charFun_conv
                (μ := (ν : Measure ℝ))
                (ν := (reflectedLaw ν : Measure ℝ))
                t)
    _ = charFun (ν : Measure ℝ) t * conj (charFun (ν : Measure ℝ) t) := by
          rw [charFun_reflectedLaw]

/-- Helper for Exercise 16.2.1: if the symmetrized law `μ * μ⁻` is Dirac, then `μ` itself is
already Dirac. -/
lemma eq_diracProba_of_symmetrizedLaw_eq_diracProba
    {x : ℝ} (hσ : symmetrizedLaw μ = diracProba x) :
    ∃ y : ℝ, μ = diracProba y := by
  let t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have ht_antitone : Antitone fun k ↦ |t k| := by
    -- Proof comment: the reciprocal test sequence decreases monotonically to `0`.
    intro m n hmn
    simp only [t]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
      (Nat.one_div_le_one_div (α := ℝ) hmn)
  have ht : Tendsto t atTop (𝓝 0) := by
    -- Proof comment: the same reciprocal sequence tends to `0`.
    have hone :
        Tendsto (fun k : ℕ ↦ (1 / ((k : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [t] using hone
  have ht_zero : Tendsto (fun k ↦ |t k|) atTop (𝓝 0) := by
    convert ht using 1
    ext k
    have hk : 0 ≤ t k := by
      dsimp [t]
      positivity
    exact abs_of_nonneg hk
  have ht_nonzero : ∀ k, t k ≠ 0 := by
    intro k
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    simp [t, hk]
  have hφ_unit : ∀ k, ‖charFun (μ : Measure ℝ) (t k)‖ = 1 := by
    intro k
    have hσ_unit : ‖charFun (symmetrizedLaw μ : Measure ℝ) (t k)‖ = 1 := by
      -- Proof comment: a Dirac law has characteristic function of unit modulus everywhere.
      calc
        ‖charFun (symmetrizedLaw μ : Measure ℝ) (t k)‖
            = ‖charFun (diracProba x : Measure ℝ) (t k)‖ := by
                rw [hσ]
        _ = 1 := by
              simp [MeasureTheory.diracProba]
    have hsq : ‖charFun (μ : Measure ℝ) (t k)‖ ^ 2 = 1 := by
      calc
        ‖charFun (μ : Measure ℝ) (t k)‖ ^ 2
            = ‖charFun (μ : Measure ℝ) (t k) *
                conj (charFun (μ : Measure ℝ) (t k))‖ := by
                  rw [norm_mul, Complex.norm_conj, sq]
        _ = ‖charFun (symmetrizedLaw μ : Measure ℝ) (t k)‖ := by
              rw [← charFun_symmetrizedLaw]
        _ = 1 := hσ_unit
    have hnonneg : 0 ≤ ‖charFun (μ : Measure ℝ) (t k)‖ := norm_nonneg _
    exact (pow_eq_one_iff_of_nonneg hnonneg (by decide : (2 : ℕ) ≠ 0)).1 hsq
  obtain ⟨y, hy⟩ :=
    Measure.eq_dirac_of_charFun_norm_eq_one_along_zero ht_antitone ht_zero ht_nonzero hφ_unit
  refine ⟨y, ?_⟩
  -- Proof comment: upgrade the measure-level Dirac conclusion back to the probability-law owner.
  apply ProbabilityMeasure.toMeasure_injective
  simpa [MeasureTheory.diracProba] using hy

/-- Helper for Exercise 16.2.1: broad `α`-stability becomes strict `α`-stability after
symmetrization, because the centering phases cancel in the characteristic function. -/
lemma symmetrizedLaw_isStrictlyStableWithIndex_of_broad
    (hμ : IsBroadlyStableWithIndex μ α) :
    IsStrictlyStableWithIndex (symmetrizedLaw μ) α := by
  rcases hμ with ⟨hαpos, hμ_nontrivial, d, hd⟩
  refine ⟨hαpos, ?_, ?_⟩
  · -- Proof comment: a Dirac symmetrization would force the original law to be Dirac.
    intro x hσ
    rcases eq_diracProba_of_symmetrizedLaw_eq_diracProba (μ := μ) hσ with ⟨y, hy⟩
    exact hμ_nontrivial y hy
  · intro n
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_charFun
    funext t
    let scale : ℝ := (n : ℝ) ^ (1 / α)
    have hscale :
        charFun (μ : Measure ℝ) (scale * t) * Complex.exp (d n * t * Complex.I) =
          charFun (μ : Measure ℝ) t ^ (n : ℕ) := by
      -- Proof comment: evaluate the broad scaling identity at the frequency `t`.
      have hchar :=
        congrArg (fun ρ : ProbabilityMeasure ℝ ↦ charFun (ρ : Measure ℝ) t) (hd n)
      calc
        charFun (μ : Measure ℝ) (scale * t) * Complex.exp (d n * t * Complex.I)
            = charFun (Measure.map (fun x : ℝ ↦ scale * x + d n) (μ : Measure ℝ)) t := by
                simpa [scale] using (charFun_map_affine μ scale (d n) t).symm
        _ = charFun ((μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t := by
              simpa [measurable_affineMap, scale] using hchar.symm
        _ = charFun (μ : Measure ℝ) t ^ (n : ℕ) := by
              simp [charFun_pow_eq_pow]
    have hphase :
        Complex.exp (d n * t * Complex.I) *
          conj (Complex.exp (d n * t * Complex.I)) = 1 := by
      -- Proof comment: the broad centering phase has unit modulus, so it disappears after
      -- symmetrization.
      have hnorm :
          ‖Complex.exp (d n * t * Complex.I)‖ = 1 := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          Complex.norm_exp_ofReal_mul_I (d n * t)
      calc
        Complex.exp (d n * t * Complex.I) *
            conj (Complex.exp (d n * t * Complex.I))
            = ‖Complex.exp (d n * t * Complex.I)‖ ^ 2 := by
                simpa using Complex.mul_conj' (Complex.exp (d n * t * Complex.I))
        _ = 1 := by
              rw [hnorm]
              norm_num
    have hsymmScale :
        charFun (symmetrizedLaw μ : Measure ℝ) (scale * t) =
          charFun (symmetrizedLaw μ : Measure ℝ) t ^ (n : ℕ) := by
      have hsq := congrArg (fun z : ℂ ↦ z * conj z) hscale
      calc
        charFun (symmetrizedLaw μ : Measure ℝ) (scale * t)
            = charFun (μ : Measure ℝ) (scale * t) *
                conj (charFun (μ : Measure ℝ) (scale * t)) := by
                  rw [charFun_symmetrizedLaw]
        _ = (charFun (μ : Measure ℝ) (scale * t) *
              conj (charFun (μ : Measure ℝ) (scale * t))) *
              (Complex.exp (d n * t * Complex.I) *
                conj (Complex.exp (d n * t * Complex.I))) := by
                  rw [hphase, mul_one]
        _ = (charFun (μ : Measure ℝ) (scale * t) * Complex.exp (d n * t * Complex.I)) *
              conj (charFun (μ : Measure ℝ) (scale * t) *
                Complex.exp (d n * t * Complex.I)) := by
                  simp [mul_comm, mul_left_comm, mul_assoc]
        _ = charFun (μ : Measure ℝ) t ^ (n : ℕ) *
              conj (charFun (μ : Measure ℝ) t ^ (n : ℕ)) := by
                exact hsq
        _ = (charFun (μ : Measure ℝ) t *
              conj (charFun (μ : Measure ℝ) t)) ^ (n : ℕ) := by
              simp [← mul_pow]
        _ = charFun (symmetrizedLaw μ : Measure ℝ) t ^ (n : ℕ) := by
              rw [charFun_symmetrizedLaw]
    -- Proof comment: the symmetrized scaling identity identifies the `n`th convolution power with
    -- the canonical zero-translation affine image.
    calc
      charFun (((symmetrizedLaw μ) ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t
          = charFun (symmetrizedLaw μ : Measure ℝ) t ^ (n : ℕ) := by
              simp [charFun_pow_eq_pow]
      _ = charFun (symmetrizedLaw μ : Measure ℝ) (scale * t) := hsymmScale.symm
      _ = charFun
            (((symmetrizedLaw μ).map
              (measurable_affineMap scale 0).aemeasurable : ProbabilityMeasure ℝ)
              : Measure ℝ) t := by
            symm
            simpa [measurable_affineMap, scale] using
              (MeasureTheory.charFun_map_mul
                (μ := (symmetrizedLaw μ : Measure ℝ)) scale t)

/-- Helper for Exercise 16.2.1: a strict scaling law forces the characteristic function to be
globally nonzero. -/
lemma strictStable_charFun_ne_zero
    (hμ : IsStrictlyStableWithIndex μ α) (t : ℝ) :
    charFun (μ : Measure ℝ) t ≠ 0 := by
  have hchar0 : charFun (μ : Measure ℝ) 0 = (1 : ℂ) := by
    simp
  have hnear :
      {u : ℝ | charFun (μ : Measure ℝ) u ∈ Metric.ball (1 : ℂ) (1 / 2)} ∈ 𝓝 (0 : ℝ) := by
    -- Proof comment: continuity at `0` gives a small neighborhood where `charFun μ` stays inside
    -- the radius-`1/2` ball around `1`, hence away from `0`.
    have hball : Metric.ball (1 : ℂ) (1 / 2) ∈ 𝓝 (charFun (μ : Measure ℝ) 0) := by
      simpa [hchar0] using Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)
    exact (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ))).continuousAt.tendsto hball
  rcases Metric.mem_nhds_iff.mp hnear with ⟨ε, hεpos, hεsubset⟩
  have hsmall_nonzero :
      ∀ u : ℝ, |u| < ε → charFun (μ : Measure ℝ) u ≠ 0 := by
    intro u hu
    have huball : u ∈ Metric.ball (0 : ℝ) ε := by
      simpa [Metric.mem_ball, Real.dist_eq] using hu
    have hclose : charFun (μ : Measure ℝ) u ∈ Metric.ball (1 : ℂ) (1 / 2) := hεsubset huball
    intro hu_zero
    have hnorm : ‖(0 : ℂ) - 1‖ < (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm, hu_zero] using hclose
    norm_num at hnorm
  by_contra hzero
  obtain ⟨m, hm⟩ := exists_nat_gt ((|t| / ε) ^ α)
  have hmpos : 0 < m := by
    have hnonneg : 0 ≤ (|t| / ε) ^ α := by positivity
    exact Nat.cast_pos.mp (lt_of_le_of_lt hnonneg hm)
  let n : ℕ+ := ⟨m, hmpos⟩
  let scale : ℝ := (n : ℝ) ^ (1 / α)
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  have hsmall_scaled : |t / scale| < ε := by
    -- Proof comment: choose `n` so that the scaled-down frequency lands inside the nonvanishing
    -- neighborhood.
    have hroot :
        |t| / ε < scale := by
      dsimp [scale]
      simpa [one_div] using
        (Real.lt_rpow_inv_iff_of_pos (show 0 ≤ |t| / ε by positivity)
          (show 0 ≤ (n : ℝ) by positivity) hμ.1).2 (by simpa [n] using hm)
    have hmul : |t| < scale * ε := (div_lt_iff₀ hεpos).mp hroot
    have hdiv : |t| / scale < ε := (div_lt_iff₀ hscale_pos).2 (by simpa [mul_comm] using hmul)
    simpa [abs_div, abs_of_pos hscale_pos] using hdiv
  have hbase_ne : charFun (μ : Measure ℝ) (t / scale) ≠ 0 :=
    hsmall_nonzero (t / scale) hsmall_scaled
  have hscaled :
      charFun (μ : Measure ℝ) t =
        charFun (μ : Measure ℝ) (t / scale) ^ (n : ℕ) := by
    -- Proof comment: rewrite the exact scaling law at the scaled-down frequency.
    have hscale_mul : scale * (t / scale) = t := by
      field_simp [scale, hscale_pos.ne']
    have hscaled' :
        charFun (μ : Measure ℝ) (scale * (t / scale)) =
          charFun (μ : Measure ℝ) (t / scale) ^ (n : ℕ) := by
      simpa [scale] using strictStable_charFunScaling hμ n (t / scale)
    rw [hscale_mul] at hscaled'
    exact hscaled'
  rw [hscaled] at hzero
  exact hbase_ne (eq_zero_of_pow_eq_zero hzero)

/-- Helper for Exercise 16.2.1: the globally nonvanishing strict-stable characteristic function
admits a continuous logarithmic lift. -/
lemma strictStable_exists_charFunExpLift
    (hμ : IsStrictlyStableWithIndex μ α) :
    ∃ Ψ : C(ℝ, ℂ), Ψ 0 = 0 ∧
      ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t := by
  -- Proof comment: once `charFun μ` is globally nonzero, the Chapter 16 covering-space lift
  -- theorem produces a continuous logarithm on the whole real line.
  have hchar0 : charFun (μ : Measure ℝ) 0 = (1 : ℂ) := by
    simp
  obtain ⟨Ψ, hΨ, _⟩ :=
    existsUnique_continuousExpLift
      (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ)))
      (strictStable_charFun_ne_zero hμ)
      hchar0
  exact ⟨Ψ, hΨ.1, hΨ.2⟩

/-- Helper for Exercise 16.2.1: the logarithmic lift of a strict-stable characteristic function
inherits the same exact scaling identity. -/
lemma strictStable_charFunLift_scaling
    (hμ : IsStrictlyStableWithIndex μ α)
    {Ψ : C(ℝ, ℂ)}
    (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (n : ℕ+) (t : ℝ) :
    Ψ (((n : ℝ) ^ (1 / α)) * t) = (n : ℂ) * Ψ t := by
  let scale : ℝ := (n : ℝ) ^ (1 / α)
  let φn : ℝ → ℂ := fun s ↦ charFun (μ : Measure ℝ) (scale * s)
  have hφn_cont : Continuous φn :=
    (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ))).comp
      (continuous_const.mul continuous_id)
  have hφn_nonzero : ∀ s : ℝ, φn s ≠ 0 := by
    intro s
    exact strictStable_charFun_ne_zero hμ (scale * s)
  have hφn_zero : φn 0 = 1 := by
    simp [φn, scale]
  obtain ⟨Φ, hΦ, hΦuniq⟩ := existsUnique_continuousExpLift hφn_cont hφn_nonzero hφn_zero
  let leftLift : C(ℝ, ℂ) :=
    ⟨fun s ↦ Ψ (scale * s), Ψ.continuous.comp (continuous_const.mul continuous_id)⟩
  have hleftLift : leftLift = Φ := by
    -- Proof comment: `s ↦ Ψ (scale * s)` is one lift of the rescaled characteristic function.
    apply hΦuniq
    constructor
    · simpa [leftLift, scale] using hΨ0
    · intro s
      simpa [leftLift, φn] using hΨexp (scale * s)
  let rightLift : C(ℝ, ℂ) :=
    ⟨fun s ↦ (n : ℂ) * Ψ s, continuous_const.mul Ψ.continuous⟩
  have hrightLift : rightLift = Φ := by
    -- Proof comment: `s ↦ n Ψ(s)` is the competing lift, and the strict scaling identity shows
    -- it exponentiates to the same target function.
    apply hΦuniq
    constructor
    · simp [rightLift, hΨ0]
    · intro s
      calc
        Complex.exp ((n : ℂ) * Ψ s)
            = Complex.exp (Ψ s) ^ (n : ℕ) := by
                simpa [mul_comm] using (Complex.exp_nat_mul (Ψ s) (n : ℕ))
        _ = charFun (μ : Measure ℝ) (scale * s) := by
              rw [hΨexp, strictStable_charFunScaling hμ n s]
        _ = φn s := rfl
  have hcomp :=
    congrArg (fun f : C(ℝ, ℂ) ↦ f t) (hleftLift.trans hrightLift.symm)
  simpa [leftLift, rightLift, scale] using hcomp

/-- Helper for Exercise 16.2.1: the `n`th convolution power of a Dirac probability law at `x` is
the Dirac law at `(n : ℝ) * x`. -/
lemma diracProba_pow (x : ℝ) (n : ℕ) :
    (diracProba x : ProbabilityMeasure ℝ) ^ n = diracProba ((n : ℝ) * x) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih]
      apply ProbabilityMeasure.toMeasure_injective
      calc
        (diracProba ((n : ℝ) * x) : Measure ℝ) ∗ (diracProba x : Measure ℝ)
            = Measure.dirac (((n : ℝ) * x) + x) := by
                rw [MeasureTheory.diracProba, MeasureTheory.diracProba]
                exact Measure.dirac_conv_dirac ((n : ℝ) * x) x
        _ = (diracProba (((n + 1 : ℕ) : ℝ) * x) : Measure ℝ) := by
              rw [MeasureTheory.diracProba]
              congr 1
              calc
                (n : ℝ) * x + x = ((n : ℝ) + 1) * x := by ring
                _ = (((n + 1 : ℕ) : ℝ)) * x := by norm_num

/-- Helper for Exercise 16.2.1: iterating the universal doubling-defect inequality gives control
at every dyadic scale. -/
lemma oneSubReCharFun_natScale_le_pow_four_mul
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (n : ℕ) (t : ℝ) :
    1 - Complex.re (charFun ν (((2 ^ n : ℕ) : ℝ) * t)) ≤
      (4 : ℝ) ^ n * (1 - Complex.re (charFun ν t)) := by
  induction n with
  | zero =>
      -- Proof comment: the zeroth dyadic scale is the original frequency.
      simp
  | succ n ihn =>
      -- Proof comment: apply the one-step doubling inequality at the already scaled frequency.
      calc
        1 - Complex.re (charFun ν (((2 ^ (n + 1) : ℕ) : ℝ) * t))
            = 1 - Complex.re (charFun ν (2 * (((2 ^ n : ℕ) : ℝ) * t))) := by
                norm_num [pow_succ, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ 4 * (1 - Complex.re (charFun ν (((2 ^ n : ℕ) : ℝ) * t))) := by
              simpa using oneSubReCharFun_double_le_four_mul (μ := ν) (((2 ^ n : ℕ) : ℝ) * t)
        _ ≤ 4 * ((4 : ℝ) ^ n * (1 - Complex.re (charFun ν t))) := by
              exact mul_le_mul_of_nonneg_left ihn (by positivity)
        _ = (4 : ℝ) ^ (n + 1) * (1 - Complex.re (charFun ν t)) := by
              ring

/-- Helper for Exercise 16.2.1: if the characteristic function is flatter than quadratic near
`0`, then the law must be `δ₀`. -/
lemma smallFrequencyFlatness_implies_diracZero_of_two_lt
    {ν : ProbabilityMeasure ℝ} {β : ℝ}
    (hβ : 2 < β)
    (hflat :
      ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, |t| < δ →
        ‖charFun (ν : Measure ℝ) t - 1‖ ≤ C * Real.rpow |t| β) :
    (ν : Measure ℝ) = Measure.dirac 0 := by
  rcases hflat with ⟨C, hC, δ, hδ, hflat⟩
  let freq : ℕ → ℝ := fun n ↦ δ / (((2 ^ (n + 1) : ℕ) : ℝ))
  have hfreq_pos : ∀ n : ℕ, 0 < freq n := by
    intro n
    dsimp [freq]
    positivity
  have hfreq_lt : ∀ n : ℕ, |freq n| < δ := by
    intro n
    have hden_pos : 0 < (((2 ^ (n + 1) : ℕ) : ℝ)) := by positivity
    have hden_gt : (1 : ℝ) < (((2 ^ (n + 1) : ℕ) : ℝ)) := by
      exact_mod_cast
        (Nat.one_lt_pow (Nat.succ_ne_zero n) (show 1 < 2 by decide))
    rw [abs_of_pos (hfreq_pos n)]
    have hmul : δ < δ * (((2 ^ (n + 1) : ℕ) : ℝ)) := by
      simpa [one_mul, mul_assoc, mul_left_comm, mul_comm] using
        (mul_lt_mul_of_pos_left hden_gt hδ)
    exact (div_lt_iff₀ hden_pos).2 hmul
  have hφ_one : ∀ n : ℕ, charFun (ν : Measure ℝ) (freq n) = 1 := by
    intro n
    have hdefect_nonneg : 0 ≤ 1 - Complex.re (charFun (ν : Measure ℝ) (freq n)) := by
      have hnorm : ‖charFun (ν : Measure ℝ) (freq n)‖ ≤ 1 :=
        MeasureTheory.norm_charFun_le_one (μ := (ν : Measure ℝ)) (freq n)
      exact sub_nonneg.mpr ((Complex.re_le_norm _).trans hnorm)
    have hbound_m :
        ∀ m : ℕ,
          1 - Complex.re (charFun (ν : Measure ℝ) (freq n)) ≤
            C * Real.rpow |freq n| β * ((2 : ℝ) ^ (2 - β)) ^ m := by
      intro m
      have hscale :=
        oneSubReCharFun_natScale_le_pow_four_mul
          (ν := (ν : Measure ℝ)) m (freq (n + m))
      have hsmall := hflat (freq (n + m)) (hfreq_lt (n + m))
      have hnorm_re :
          1 - Complex.re (charFun (ν : Measure ℝ) (freq (n + m))) ≤
            ‖charFun (ν : Measure ℝ) (freq (n + m)) - 1‖ := by
        have hreal :
            1 - Complex.re (charFun (ν : Measure ℝ) (freq (n + m))) ≤
              ‖1 - charFun (ν : Measure ℝ) (freq (n + m))‖ := by
          simpa using (Complex.re_le_norm (1 - charFun (ν : Measure ℝ) (freq (n + m))))
        simpa [norm_sub_rev] using hreal
      have hfreq_scale :
          (((2 ^ m : ℕ) : ℝ) * freq (n + m)) = freq n := by
        dsimp [freq]
        rw [show (((2 ^ (n + m + 1) : ℕ) : ℝ)) =
            (((2 ^ m : ℕ) : ℝ)) * (((2 ^ (n + 1) : ℕ) : ℝ)) by
              norm_num [pow_add, pow_succ, mul_assoc, mul_left_comm, mul_comm]]
        field_simp
      calc
        1 - Complex.re (charFun (ν : Measure ℝ) (freq n))
            = 1 - Complex.re (charFun (ν : Measure ℝ) ((((2 ^ m : ℕ) : ℝ) * freq (n + m)))) := by
                rw [hfreq_scale]
        _ ≤ (4 : ℝ) ^ m *
              (1 - Complex.re (charFun (ν : Measure ℝ) (freq (n + m)))) := by
              simpa using hscale
        _ ≤ (4 : ℝ) ^ m * ‖charFun (ν : Measure ℝ) (freq (n + m)) - 1‖ := by
              gcongr
        _ ≤ (4 : ℝ) ^ m * (C * Real.rpow |freq (n + m)| β) := by
              gcongr
        _ = C * Real.rpow |freq n| β * ((2 : ℝ) ^ (2 - β)) ^ m := by
              have htwo_pos : 0 < (((2 ^ m : ℕ) : ℝ)) := by positivity
              have habs_scale :
                  |freq (n + m)| = |freq n| / (((2 ^ m : ℕ) : ℝ)) := by
                rw [abs_of_pos (hfreq_pos (n + m)), abs_of_pos (hfreq_pos n)]
                exact (eq_div_iff htwo_pos.ne').2 (by simpa [mul_comm] using hfreq_scale)
              have hdiv_rpow :
                  Real.rpow (|freq n| / (((2 ^ m : ℕ) : ℝ))) β =
                    Real.rpow |freq n| β / Real.rpow (((2 ^ m : ℕ) : ℝ)) β := by
                simpa using
                  (Real.div_rpow
                    (abs_nonneg (freq n))
                    (show 0 ≤ (((2 ^ m : ℕ) : ℝ)) by positivity) β)
              rw [habs_scale, hdiv_rpow]
              rw [div_eq_mul_inv]
              have hden :
                  (Real.rpow (((2 ^ m : ℕ) : ℝ)) β)⁻¹ = (((2 : ℝ) ^ (-β)) ^ m) := by
                calc
                  (Real.rpow (((2 ^ m : ℕ) : ℝ)) β)⁻¹
                      = (((2 : ℝ) ^ m).rpow β)⁻¹ := by
                          rw [show (((2 ^ m : ℕ) : ℝ)) = (2 : ℝ) ^ m by exact_mod_cast rfl]
                  _ = ((2 : ℝ) ^ (β * (m : ℝ)))⁻¹ := by
                        apply congrArg Inv.inv
                        calc
                          ((2 : ℝ) ^ m).rpow β = (2 : ℝ) ^ ((m : ℝ) * β) := by
                            simpa using
                              (Real.rpow_natCast_mul (show 0 ≤ (2 : ℝ) by positivity) m β).symm
                          _ = (2 : ℝ) ^ (β * (m : ℝ)) := by
                            congr 1
                            ring
                  _ = (((2 : ℝ) ^ β) ^ m)⁻¹ := by
                        rw [Real.rpow_mul_natCast (by positivity)]
                  _ = (((2 : ℝ) ^ β)⁻¹) ^ m := by rw [inv_pow]
                  _ = (((2 : ℝ) ^ (-β)) ^ m) := by
                        rw [Real.rpow_neg (show 0 ≤ (2 : ℝ) by positivity)]
              rw [hden]
              calc
                (4 : ℝ) ^ m * (C * (Real.rpow |freq n| β * (((2 : ℝ) ^ (-β)) ^ m)))
                    = C * Real.rpow |freq n| β *
                        ((4 : ℝ) ^ m * (((2 : ℝ) ^ (-β)) ^ m)) := by ring
                _ = C * Real.rpow |freq n| β * (((2 : ℝ) ^ (2 - β)) ^ m) := by
                      congr 1
                      calc
                        (4 : ℝ) ^ m * (((2 : ℝ) ^ (-β)) ^ m)
                            = ((((2 : ℝ) ^ (2 : ℝ)) * ((2 : ℝ) ^ (-β))) ^ m) := by
                                rw [show (4 : ℝ) ^ m = (((2 : ℝ) ^ (2 : ℝ)) ^ m) by norm_num,
                                  ← mul_pow]
                        _ = (((2 : ℝ) ^ ((2 : ℝ) + (-β))) ^ m) := by
                              congr 1
                              rw [← Real.rpow_add (by positivity)]
                        _ = (((2 : ℝ) ^ (2 - β)) ^ m) := by
                              simp [sub_eq_add_neg]
    have hq_lt : (2 : ℝ) ^ (2 - β) < 1 := by
      have hneg : 2 - β < 0 := by linarith
      simpa using
        (Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num) hneg)
    have hq_nonneg : 0 ≤ (2 : ℝ) ^ (2 - β) := by positivity
    have hlimit :
        Tendsto (fun m : ℕ ↦
          C * Real.rpow |freq n| β * ((2 : ℝ) ^ (2 - β)) ^ m) atTop (𝓝 0) := by
      have hpow :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt
      simpa [zero_mul] using Tendsto.const_mul (C * Real.rpow |freq n| β) hpow
    have hdefect_le_zero :
        1 - Complex.re (charFun (ν : Measure ℝ) (freq n)) ≤ 0 := by
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
        (Filter.Eventually.of_forall hbound_m)
    have hdefect_zero :
        1 - Complex.re (charFun (ν : Measure ℝ) (freq n)) = 0 :=
      le_antisymm hdefect_le_zero hdefect_nonneg
    have hre_one : Complex.re (charFun (ν : Measure ℝ) (freq n)) = 1 := by
      linarith
    have hnorm_le : ‖charFun (ν : Measure ℝ) (freq n)‖ ≤ 1 :=
      MeasureTheory.norm_charFun_le_one (μ := (ν : Measure ℝ)) (freq n)
    have hnorm_eq : ‖charFun (ν : Measure ℝ) (freq n)‖ = 1 := by
      have hnorm_ge : 1 ≤ ‖charFun (ν : Measure ℝ) (freq n)‖ := by
        have hreal_le := Complex.re_le_norm (charFun (ν : Measure ℝ) (freq n))
        linarith
      exact le_antisymm hnorm_le hnorm_ge
    have him_zero : Complex.im (charFun (ν : Measure ℝ) (freq n)) = 0 := by
      have hre_abs :
          |Complex.re (charFun (ν : Measure ℝ) (freq n))| =
            ‖charFun (ν : Measure ℝ) (freq n)‖ := by
        rw [hre_one, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), hnorm_eq]
      exact Complex.abs_re_eq_norm.mp hre_abs
    apply Complex.ext
    · exact hre_one
    · exact him_zero
  have hfreq_antitone : Antitone fun n ↦ |freq n| := by
    intro m n hmn
    have hden_pos_m : 0 < (((2 ^ (m + 1) : ℕ) : ℝ)) := by positivity
    have hden_le :
        (((2 ^ (m + 1) : ℕ) : ℝ)) ≤ (((2 ^ (n + 1) : ℕ) : ℝ)) := by
      exact_mod_cast Nat.pow_le_pow_right (show 0 < 2 by decide) (Nat.succ_le_succ hmn)
    dsimp
    rw [abs_of_pos (hfreq_pos n), abs_of_pos (hfreq_pos m)]
    exact div_le_div_of_nonneg_left (by linarith) hden_pos_m hden_le
  have hfreq_zero : Tendsto (fun n ↦ |freq n|) atTop (𝓝 0) := by
    have hpow_base : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)
    have hpow :
        Tendsto (fun n : ℕ ↦ (((2 ^ (n + 1) : ℕ) : ℝ))) atTop atTop := by
      have hpow_mul : Tendsto (fun n : ℕ ↦ 2 * (2 : ℝ) ^ n) atTop atTop :=
        Tendsto.const_mul_atTop (show (0 : ℝ) < 2 by norm_num) hpow_base
      convert hpow_mul using 1
      ext n
      norm_num [pow_succ, mul_assoc, mul_left_comm, mul_comm]
    have hdiv : Tendsto freq atTop (𝓝 0) := by
      dsimp [freq]
      simpa [div_eq_mul_inv] using Tendsto.const_mul δ (tendsto_inv_atTop_zero.comp hpow)
    have habs_eq : (fun n ↦ |freq n|) = freq := by
      funext n
      exact abs_of_pos (hfreq_pos n)
    simpa [habs_eq] using hdiv
  have hfreq_nonzero : ∀ n : ℕ, freq n ≠ 0 := by
    intro n
    exact ne_of_gt (hfreq_pos n)
  exact Measure.eq_dirac_zero_of_charFun_eq_one_along_zero
    hfreq_antitone hfreq_zero hfreq_nonzero hφ_one

-- Proof sketch: pass to the chapter owner abstraction on the admissible range via
-- `IsStrictlyStableWithIndex.toIsStableWithIndex`, rewrite the resulting scaling law on
-- characteristic functions, and choose `n` comparable to `|t|^{-α}` to obtain the Hölder bound
-- near the origin.
/-- Helper for Exercise 16.2.1: choosing `n = ⌈(δ / |t|)^α⌉` places the scaled frequency inside the
shell `[δ, 2^(1 / α) δ)` and simultaneously gives the reciprocal power bound needed in item (1).
-/
lemma existsScaleIndexMemSmallShell
    (hα : 0 < α) {δ : ℝ} (hδ : 0 < δ) {t : ℝ}
    (ht : 0 < |t|) (htlt : |t| < δ) :
    ∃ n : ℕ+, δ ≤ ((n : ℝ) ^ (1 / α)) * |t| ∧
      ((n : ℝ) ^ (1 / α)) * |t| < ((2 : ℝ) ^ (1 / α)) * δ ∧
      (n : ℝ)⁻¹ ≤ δ ^ (-α) * Real.rpow |t| α := by
  let x : ℝ := Real.rpow (δ / |t|) α
  have hquot_gt : 1 < δ / |t| := by
    exact (one_lt_div ht).2 htlt
  have hx_one : 1 < x := by
    simpa [x] using Real.one_lt_rpow hquot_gt hα
  let nNat : ℕ := Nat.ceil x
  have hnNat_pos : 0 < nNat := Nat.ceil_pos.mpr (lt_trans zero_lt_one hx_one)
  let n : ℕ+ := ⟨nNat, hnNat_pos⟩
  have hceil_lower : x ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_ceil x
  have hceil_upper : (n : ℝ) < x + 1 := by
    exact_mod_cast Nat.ceil_lt_add_one (show 0 ≤ x by positivity)
  have hceil_upper' : (n : ℝ) < 2 * x := by
    have hx_ge_one : (1 : ℝ) ≤ x := le_of_lt hx_one
    linarith
  have hroot_lower :
      δ / |t| ≤ (n : ℝ) ^ (1 / α) := by
    have hpow :=
      Real.rpow_le_rpow (show 0 ≤ x by positivity) hceil_lower
        (show 0 ≤ 1 / α by positivity)
    have hx_root : x ^ (1 / α) = δ / |t| := by
      dsimp [x]
      simpa [one_div] using
        (Real.rpow_rpow_inv (show 0 ≤ δ / |t| by positivity) hα.ne')
    rwa [hx_root] at hpow
  have hroot_upper :
      (n : ℝ) ^ (1 / α) <
        ((2 : ℝ) ^ (1 / α)) * (δ / |t|) := by
    have htmp :
        (n : ℝ) ^ (1 / α) < (2 * x) ^ (1 / α) := by
      exact Real.rpow_lt_rpow (show 0 ≤ (n : ℝ) by positivity) hceil_upper'
        (show 0 < 1 / α by positivity)
    have hrewrite :
        (2 * x) ^ (1 / α) = ((2 : ℝ) ^ (1 / α)) * (δ / |t|) := by
      dsimp [x]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      simpa [one_div] using
        congrArg (fun r : ℝ ↦ ((2 : ℝ) ^ (1 / α)) * r)
          (Real.rpow_rpow_inv (show 0 ≤ δ / |t| by positivity) hα.ne')
    rw [hrewrite] at htmp
    exact htmp
  refine ⟨n, ?_, ?_, ?_⟩
  · -- Proof comment: multiply the scaled lower bound by `|t|`.
    calc
      δ = (δ / |t|) * |t| := by field_simp [ht.ne']
      _ ≤ ((n : ℝ) ^ (1 / α)) * |t| := by gcongr
  · -- Proof comment: the ceiling upper bound yields the strict upper shell constraint.
    have hmul := mul_lt_mul_of_pos_right hroot_upper ht
    calc
      ((n : ℝ) ^ (1 / α)) * |t| < (((2 : ℝ) ^ (1 / α)) * (δ / |t|)) * |t| := hmul
      _ = ((2 : ℝ) ^ (1 / α)) * δ := by field_simp [ht.ne', mul_assoc]
  · -- Proof comment: invert the ceiling lower bound and rewrite the inverse shell scale as the
    -- target `δ^{-α} |t|^α`.
    have hInv : (n : ℝ)⁻¹ ≤ x⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (show 0 < x by linarith) hceil_lower
    calc
      (n : ℝ)⁻¹ ≤ x⁻¹ := hInv
      _ = δ ^ (-α) * Real.rpow |t| α := by
            dsimp [x]
            rw [← Real.rpow_neg (show 0 ≤ δ / |t| by positivity)]
            rw [Real.div_rpow hδ.le (abs_nonneg t) (-α)]
            rw [div_eq_mul_inv, Real.rpow_neg (abs_nonneg t)]
            rw [inv_inv]
/-- Exercise 16.2.1 (1): if a real probability law is strictly stable with index `α`, then its
characteristic function satisfies `|φ(t) - 1| ≤ C |t|^α` for all sufficiently small `t`. -/
theorem norm_charFun_sub_one_le_const_mul_rpow_of_isStrictlyStableWithIndex
    (hμ : IsStrictlyStableWithIndex μ α) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, |t| < δ →
      ‖charFun (μ : Measure ℝ) t - 1‖ ≤ C * Real.rpow |t| α := by
  obtain ⟨Ψ, hΨ0, hΨexp⟩ := strictStable_exists_charFunExpLift hμ
  let R : ℝ := (2 : ℝ) ^ (1 / α)
  have hR_pos : 0 < R := by
    dsimp [R]
    positivity
  have hΨnear :
      {u : ℝ | Ψ u ∈ Metric.ball (0 : ℂ) (1 / 2)} ∈ 𝓝 (0 : ℝ) := by
    -- Proof comment: continuity of the logarithmic lift gives a neighborhood where the lift is
    -- small enough for the first-order exponential estimate.
    have hball : Metric.ball (0 : ℂ) (1 / 2) ∈ 𝓝 (Ψ 0) := by
      simpa [hΨ0] using Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)
    exact Ψ.continuous.continuousAt.tendsto hball
  rcases Metric.mem_nhds_iff.mp hΨnear with ⟨ρ, hρpos, hρsubset⟩
  let δ : ℝ := ρ / R
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ ^ (-α), by positivity, δ, hδpos, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · -- Proof comment: the origin is immediate from `charFun μ 0 = 1`.
    subst ht0
    simp [MeasureTheory.charFun_zero, Real.zero_rpow hμ.1.ne']
  · have htabs_pos : 0 < |t| := abs_pos.mpr ht0
    obtain ⟨n, hshell_lower, hshell_upper, hInv⟩ :=
      existsScaleIndexMemSmallShell hμ.1 hδpos htabs_pos ht
    let scale : ℝ := (n : ℝ) ^ (1 / α)
    have hscale_pos : 0 < scale := by
      dsimp [scale]
      positivity
    have hscaled_small : |scale * t| < ρ := by
      have hRδ : R * δ = ρ := by
        dsimp [δ]
        field_simp [hR_pos.ne']
      calc
        |scale * t| = scale * |t| := by
          rw [abs_mul, abs_of_pos hscale_pos]
        _ < R * δ := by
              simpa [scale, R] using hshell_upper
        _ = ρ := hRδ
    have hscaled_ball : scale * t ∈ Metric.ball (0 : ℝ) ρ := by
      simpa [Metric.mem_ball, Real.dist_eq] using hscaled_small
    have hΨscaled : ‖Ψ (scale * t)‖ < (1 / 2 : ℝ) := by
      have hball : Ψ (scale * t) ∈ Metric.ball (0 : ℂ) (1 / 2) := hρsubset hscaled_ball
      simpa [Metric.mem_ball, dist_eq_norm] using hball
    have hlift := strictStable_charFunLift_scaling hμ hΨ0 hΨexp n t
    have hΨt :
        ‖Ψ t‖ ≤ ((1 / 2 : ℝ) / (n : ℝ)) := by
      have hmul :
          (n : ℝ) * ‖Ψ t‖ = ‖Ψ (scale * t)‖ := by
        calc
          (n : ℝ) * ‖Ψ t‖ = ‖((n : ℂ) * Ψ t)‖ := by
            rw [norm_mul, Complex.norm_natCast]
          _ = ‖Ψ (scale * t)‖ := by
                rw [← hlift]
      have hmul_le : (n : ℝ) * ‖Ψ t‖ ≤ (1 / 2 : ℝ) := by
        rw [hmul]
        exact le_of_lt hΨscaled
      exact (le_div_iff₀ (by positivity : 0 < (n : ℝ))).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul_le)
    have hΨt_le_one : ‖Ψ t‖ ≤ 1 := by
      have hhalf : ((1 / 2 : ℝ) / (n : ℝ)) ≤ 1 / 2 := by
        have hnpos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
        exact (div_le_iff₀ (by positivity : 0 < (n : ℝ))).2 (by nlinarith)
      have honehalf : (1 / 2 : ℝ) ≤ 1 := by norm_num
      exact le_trans hΨt (hhalf.trans honehalf)
    have hExpDiff :
        ‖charFun (μ : Measure ℝ) t - 1‖ ≤ (n : ℝ)⁻¹ := by
      calc
        ‖charFun (μ : Measure ℝ) t - 1‖ = ‖Complex.exp (Ψ t) - 1‖ := by
          rw [← hΨexp t]
        _ = ‖Ψ t + (Complex.exp (Ψ t) - 1 - Ψ t)‖ := by ring_nf
        _ ≤ ‖Ψ t‖ + ‖Complex.exp (Ψ t) - 1 - Ψ t‖ := norm_add_le _ _
        _ ≤ ‖Ψ t‖ + ‖Ψ t‖ ^ 2 := by
              gcongr
              exact Complex.norm_exp_sub_one_sub_id_le hΨt_le_one
        _ ≤ 2 * ‖Ψ t‖ := by
              have hsquare_le : ‖Ψ t‖ ^ 2 ≤ ‖Ψ t‖ := by
                simpa [pow_two] using mul_le_mul_of_nonneg_left hΨt_le_one (norm_nonneg _)
              linarith
        _ ≤ 2 * (((1 / 2 : ℝ) / (n : ℝ))) := by
              gcongr
        _ = (n : ℝ)⁻¹ := by
              field_simp [show (0 : ℝ) ≠ (n : ℝ) by positivity]
    exact le_trans hExpDiff hInv

-- Proof sketch: combine the small-frequency bound from item (1) with the second-order criterion
-- from Exercise 15.3.2; for `α > 2`, the source-facing strict `α`-stability relation forces the
-- characteristic function to be flatter than quadratic at the origin, hence the law is the Dirac
-- mass at `0`.
/-- Exercise 16.2.1 (2): a strictly stable real probability law with index `α > 2` is
necessarily the Dirac mass at `0`. -/
theorem eq_dirac_zero_of_two_lt_of_isStrictlyStableWithIndex
    (hμ : IsStrictlyStableWithIndex μ α) (hα : 2 < α) :
    (μ : Measure ℝ) = Measure.dirac 0 := by
  -- Proof comment: item (1) gives a flatter-than-quadratic small-frequency bound, so the
  -- abstract flatness criterion forces the law to be `δ₀`.
  rcases norm_charFun_sub_one_le_const_mul_rpow_of_isStrictlyStableWithIndex hμ with
    ⟨C, hC, δ, hδ, hbound⟩
  exact smallFrequencyFlatness_implies_diracZero_of_two_lt hα ⟨C, hC, δ, hδ, hbound⟩

-- Proof sketch: adapt the argument from item (2) to the source-facing affine scaling relation for
-- broad `α`-stability, absorbing the centering term into the characteristic-function identity and
-- then applying the same quadratic flatness criterion at the origin.
/-- Exercise 16.2.1 (3): a broadly stable real probability law with index `α > 2` is
necessarily the Dirac mass at `0`. -/
theorem eq_dirac_zero_of_two_lt_of_isBroadlyStableWithIndex
    (hμ : IsBroadlyStableWithIndex μ α) (hα : 2 < α) :
    (μ : Measure ℝ) = Measure.dirac 0 := by
  -- Route correction: instead of carrying the centering phases through the small-frequency
  -- estimate directly, symmetrize first so the broad phases cancel at the characteristic-function
  -- level and item (2) applies verbatim.
  have hσ : IsStrictlyStableWithIndex (symmetrizedLaw μ) α :=
    symmetrizedLaw_isStrictlyStableWithIndex_of_broad hμ
  have hσdirac :
      (symmetrizedLaw μ : Measure ℝ) = Measure.dirac 0 :=
    eq_dirac_zero_of_two_lt_of_isStrictlyStableWithIndex hσ hα
  have hσdiracProba : symmetrizedLaw μ = diracProba 0 := by
    -- Proof comment: convert the measure-level Dirac conclusion back to the probability-law
    -- owner so the symmetrization helper applies directly.
    apply ProbabilityMeasure.toMeasure_injective
    simpa [symmetrizedLaw, MeasureTheory.diracProba] using hσdirac
  rcases eq_diracProba_of_symmetrizedLaw_eq_diracProba (μ := μ) hσdiracProba with ⟨b, hb⟩
  exact (hμ.2.1 b hb).elim

end MeasureTheory.ProbabilityMeasure
