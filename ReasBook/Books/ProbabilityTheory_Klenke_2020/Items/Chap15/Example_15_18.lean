/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_12

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/- Example 15.18 uses the triangular characteristic-function formula from Theorem 15.12 at
`a = π / 2`. -/
local notation "φΔ" => charFun (triangularCharacteristicMeasure (Real.pi / 2))
local notation "IΔ" => Set.Icc (-Real.pi / 2) (Real.pi / 2)

/-- Helper for Example 15.18: the triangular characteristic function at `a = π / 2` vanishes
outside `IΔ`. -/
lemma triangularCharFun_piHalf_eq_zero_of_not_memIΔ {t : ℝ} (ht : t ∉ IΔ) :
    φΔ t = 0 := by
  have hpi2 : 0 < Real.pi / 2 := by
    positivity
  -- Normalize `t ∉ IΔ` to the failure of the absolute-value bound in the tent formula.
  have hnotAbs : ¬ |t| ≤ Real.pi / 2 := by
    intro habs
    have hbounds := abs_le.mp habs
    have hleft : -Real.pi / 2 ≤ t := by
      simpa [neg_div] using hbounds.1
    apply ht
    exact ⟨hleft, hbounds.2⟩
  rw [charFun_triangularCharacteristicMeasure (Real.pi / 2) hpi2 t]
  -- The tent profile is zero once `|t| / (π / 2) ≥ 1`.
  have hratio : 1 ≤ |t| / (Real.pi / 2) := by
    rw [one_le_div hpi2]
    exact le_of_not_ge hnotAbs
  have hnonpos : 1 - |t| / (Real.pi / 2) ≤ 0 := by
    linarith
  simp [max_eq_right hnonpos]

-- Proof sketch: use the canonical owner `φΔ = charFun (triangularCharacteristicMeasure (π / 2))`.
-- If `t ∈ IΔ`, use `hψ_eq`; if `t ∉ IΔ`, the owner characteristic function vanishes,
-- since `charFun_triangularCharacteristicMeasure` specializes to the tent function there.
/-- If a characteristic function agrees on `[-π / 2, π / 2]` with the triangular characteristic
function from Example 15.15 at `a = π / 2`, then their products with that characteristic function
agree everywhere. -/
theorem example1518TriangularCharFun_mul_eq_of_agreesOn
    {ψ : ℝ → ℂ}
    (hψ_eq : Set.EqOn ψ φΔ IΔ) :
    φΔ * φΔ = φΔ * ψ := by
  ext t
  by_cases ht : t ∈ IΔ
  · -- On `IΔ`, the two right factors agree by hypothesis.
    simp [Pi.mul_apply, hψ_eq ht]
  · -- Off `IΔ`, the common factor `φΔ t` vanishes.
    have hzero : φΔ t = 0 := triangularCharFun_piHalf_eq_zero_of_not_memIΔ ht
    simp [Pi.mul_apply, hzero]

/-- Helper for Example 15.18: the sums `X + Y` and `X + Z` have the same pushforward law once
their characteristic functions agree through the triangular factor `φΔ`. -/
lemma sumLaw_eq_of_triangular_charFun_agreement
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y Z : Ω → ℝ}
    (hX_meas : Measurable X) (hY_meas : Measurable Y) (hZ_meas : Measurable Z)
    (h_indep : iIndepFun (![X, Y, Z] : Fin 3 → Ω → ℝ) P)
    {ψ : ℝ → ℂ}
    (hψ_eq : Set.EqOn ψ φΔ IΔ)
    (hφX : charFun (P.map X) = φΔ)
    (hφY : charFun (P.map Y) = φΔ)
    (hφZ : charFun (P.map Z) = ψ) :
    P.map (fun ω ↦ X ω + Y ω) = P.map (fun ω ↦ X ω + Z ω) := by
  have hXY : IndepFun X Y P := by
    -- Extract the pairwise independence of `(X, Y)` from the triple independence hypothesis.
    simpa using h_indep.indepFun (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
  have hXZ : IndepFun X Z P := by
    -- Extract the pairwise independence of `(X, Z)` in the same way.
    simpa using h_indep.indepFun (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  refine Measure.ext_of_charFun ?_
  ext t
  -- Compare the two sum characteristic functions and rewrite them through the pointwise product
  -- identity from `example1518TriangularCharFun_mul_eq_of_agreesOn`.
  calc
    charFun (P.map (fun ω ↦ X ω + Y ω)) t =
        (charFun (P.map X) * charFun (P.map Y)) t := by
      simpa using
        congrArg (fun f : ℝ → ℂ ↦ f t)
          (hXY.charFun_map_fun_add_eq_mul hX_meas.aemeasurable hY_meas.aemeasurable)
    _ = (φΔ * φΔ) t := by rw [hφX, hφY]
    _ = (φΔ * ψ) t := by
      simpa using
        congrArg (fun f : ℝ → ℂ ↦ f t)
          (example1518TriangularCharFun_mul_eq_of_agreesOn (ψ := ψ) hψ_eq)
    _ = (charFun (P.map X) * charFun (P.map Z)) t := by rw [hφX, hφZ]
    _ = charFun (P.map (fun ω ↦ X ω + Z ω)) t := by
      simpa using
        congrArg (fun f : ℝ → ℂ ↦ f t)
          (hXZ.charFun_map_fun_add_eq_mul hX_meas.aemeasurable hZ_meas.aemeasurable).symm

-- Proof sketch: use independence to identify the characteristic functions of `X + Y` and `X + Z`
-- for the measurable random variables `X`, `Y`, and `Z` with the products `φ_X φ_Y` and
-- `φ_X φ_Z`. Rewrite these using the hypotheses
-- `φ_X = φ_Y = φΔ` and `φ_Z = ψ`, apply
-- `example1518TriangularCharFun_mul_eq_of_agreesOn`, and then use uniqueness of characteristic
-- functions for probability measures. If `Y` and `Z` were identically distributed, then their
-- pushforward
-- laws would have the same characteristic function, contradicting `hψ_ne`.
/-- Example 15.18: if `X`, `Y`, and `Z` are independent measurable real random variables with
`φ_X = φ_Y = charFun (triangularCharacteristicMeasure (π / 2))`, with `φ_Z = ψ`, and if `ψ`
agrees with this characteristic function on `[-π / 2, π / 2]` but is not equal to it, then
`X + Y` and `X + Z` are identically distributed although `Y` and `Z` are not. -/
theorem same_sum_not_identDistrib_of_triangular_charFun
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y Z : Ω → ℝ}
    (hX_meas : Measurable X) (hY_meas : Measurable Y) (hZ_meas : Measurable Z)
    (h_indep : iIndepFun (![X, Y, Z] : Fin 3 → Ω → ℝ) P)
    {ψ : ℝ → ℂ}
    (hψ_eq : Set.EqOn ψ φΔ IΔ)
    (hψ_ne : ψ ≠ φΔ)
    (hφX : charFun (P.map X) = φΔ)
    (hφY : charFun (P.map Y) = φΔ)
    (hφZ : charFun (P.map Z) = ψ) :
    IdentDistrib (fun ω ↦ X ω + Y ω) (fun ω ↦ X ω + Z ω) P P ∧
      ¬ IdentDistrib Y Z P P := by
  constructor
  · -- Package the pushforward-law equality into the `IdentDistrib` structure.
    refine
      { aemeasurable_fst := (hX_meas.add hY_meas).aemeasurable
        aemeasurable_snd := (hX_meas.add hZ_meas).aemeasurable
        map_eq := sumLaw_eq_of_triangular_charFun_agreement hX_meas hY_meas hZ_meas h_indep hψ_eq
          hφX hφY hφZ }
  · intro hYZ
    -- If `Y` and `Z` had the same law, then their characteristic functions would coincide.
    have hchar : φΔ = ψ := by
      simpa [hφY, hφZ] using congrArg charFun hYZ.map_eq
    exact hψ_ne hchar.symm
