/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FiniteChecks
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk00
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk01
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk02
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk03
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk04
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk05
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk06
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk07
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk08
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk09
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk10
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk11
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk12
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk13
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk14
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk15
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk16
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk17
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk18
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk19
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk20
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk21
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk22
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk23
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk24
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk25
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk26
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk27
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk28
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk29
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk30
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk31
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00Chunk32

@[expose] public section

set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.Leaves

theorem diagonal00Identity : diagonalAffine00 = diagonalExpansion00 := by
  apply list_eq_of_getD _ _ 0 257 diagonalAffine00_length diagonalExpansion00_length
  intro i
  by_cases h0 : i.val < 8
  · exact diagonal00Chunk00 ⟨i.val, h0⟩
  ·
    by_cases h1 : i.val < 16
    · have he := diagonal00Chunk01 ⟨i.val - 8, by omega⟩
      simpa only [Nat.sub_add_cancel (show 8 ≤ i.val by omega)] using he
    ·
      by_cases h2 : i.val < 24
      · have he := diagonal00Chunk02 ⟨i.val - 16, by omega⟩
        simpa only [Nat.sub_add_cancel (show 16 ≤ i.val by omega)] using he
      ·
        by_cases h3 : i.val < 32
        · have he := diagonal00Chunk03 ⟨i.val - 24, by omega⟩
          simpa only [Nat.sub_add_cancel (show 24 ≤ i.val by omega)] using he
        ·
          by_cases h4 : i.val < 40
          · have he := diagonal00Chunk04 ⟨i.val - 32, by omega⟩
            simpa only [Nat.sub_add_cancel (show 32 ≤ i.val by omega)] using he
          ·
            by_cases h5 : i.val < 48
            · have he := diagonal00Chunk05 ⟨i.val - 40, by omega⟩
              simpa only [Nat.sub_add_cancel (show 40 ≤ i.val by omega)] using he
            ·
              by_cases h6 : i.val < 56
              · have he := diagonal00Chunk06 ⟨i.val - 48, by omega⟩
                simpa only [Nat.sub_add_cancel (show 48 ≤ i.val by omega)] using he
              ·
                by_cases h7 : i.val < 64
                · have he := diagonal00Chunk07 ⟨i.val - 56, by omega⟩
                  simpa only [Nat.sub_add_cancel (show 56 ≤ i.val by omega)] using he
                ·
                  by_cases h8 : i.val < 72
                  · have he := diagonal00Chunk08 ⟨i.val - 64, by omega⟩
                    simpa only [Nat.sub_add_cancel (show 64 ≤ i.val by omega)] using he
                  ·
                    by_cases h9 : i.val < 80
                    · have he := diagonal00Chunk09 ⟨i.val - 72, by omega⟩
                      simpa only [Nat.sub_add_cancel (show 72 ≤ i.val by omega)] using he
                    ·
                      by_cases h10 : i.val < 88
                      · have he := diagonal00Chunk10 ⟨i.val - 80, by omega⟩
                        simpa only [Nat.sub_add_cancel (show 80 ≤ i.val by omega)] using he
                      ·
                        by_cases h11 : i.val < 96
                        · have he := diagonal00Chunk11 ⟨i.val - 88, by omega⟩
                          simpa only [Nat.sub_add_cancel (show 88 ≤ i.val by omega)] using he
                        ·
                          by_cases h12 : i.val < 104
                          · have he := diagonal00Chunk12 ⟨i.val - 96, by omega⟩
                            simpa only [Nat.sub_add_cancel (show 96 ≤ i.val by omega)] using he
                          ·
                            by_cases h13 : i.val < 112
                            · have he := diagonal00Chunk13 ⟨i.val - 104, by omega⟩
                              simpa only [Nat.sub_add_cancel (show 104 ≤ i.val by omega)] using he
                            ·
                              by_cases h14 : i.val < 120
                              · have he := diagonal00Chunk14 ⟨i.val - 112, by omega⟩
                                simpa only [Nat.sub_add_cancel (show 112 ≤ i.val by omega)] using he
                              ·
                                by_cases h15 : i.val < 128
                                · have he := diagonal00Chunk15 ⟨i.val - 120, by omega⟩
                                  simpa only [Nat.sub_add_cancel (show 120 ≤ i.val by omega)] using he
                                ·
                                  by_cases h16 : i.val < 136
                                  · have he := diagonal00Chunk16 ⟨i.val - 128, by omega⟩
                                    simpa only [Nat.sub_add_cancel (show 128 ≤ i.val by omega)] using he
                                  ·
                                    by_cases h17 : i.val < 144
                                    · have he := diagonal00Chunk17 ⟨i.val - 136, by omega⟩
                                      simpa only [Nat.sub_add_cancel (show 136 ≤ i.val by omega)] using he
                                    ·
                                      by_cases h18 : i.val < 152
                                      · have he := diagonal00Chunk18 ⟨i.val - 144, by omega⟩
                                        simpa only [Nat.sub_add_cancel (show 144 ≤ i.val by omega)] using he
                                      ·
                                        by_cases h19 : i.val < 160
                                        · have he := diagonal00Chunk19 ⟨i.val - 152, by omega⟩
                                          simpa only [Nat.sub_add_cancel (show 152 ≤ i.val by omega)] using he
                                        ·
                                          by_cases h20 : i.val < 168
                                          · have he := diagonal00Chunk20 ⟨i.val - 160, by omega⟩
                                            simpa only [Nat.sub_add_cancel (show 160 ≤ i.val by omega)] using he
                                          ·
                                            by_cases h21 : i.val < 176
                                            · have he := diagonal00Chunk21 ⟨i.val - 168, by omega⟩
                                              simpa only [Nat.sub_add_cancel (show 168 ≤ i.val by omega)] using he
                                            ·
                                              by_cases h22 : i.val < 184
                                              · have he := diagonal00Chunk22 ⟨i.val - 176, by omega⟩
                                                simpa only [Nat.sub_add_cancel (show 176 ≤ i.val by omega)] using he
                                              ·
                                                by_cases h23 : i.val < 192
                                                · have he := diagonal00Chunk23 ⟨i.val - 184, by omega⟩
                                                  simpa only [Nat.sub_add_cancel (show 184 ≤ i.val by omega)] using he
                                                ·
                                                  by_cases h24 : i.val < 200
                                                  · have he := diagonal00Chunk24 ⟨i.val - 192, by omega⟩
                                                    simpa only [Nat.sub_add_cancel (show 192 ≤ i.val by omega)] using he
                                                  ·
                                                    by_cases h25 : i.val < 208
                                                    · have he := diagonal00Chunk25 ⟨i.val - 200, by omega⟩
                                                      simpa only [Nat.sub_add_cancel (show 200 ≤ i.val by omega)] using he
                                                    ·
                                                      by_cases h26 : i.val < 216
                                                      · have he := diagonal00Chunk26 ⟨i.val - 208, by omega⟩
                                                        simpa only [Nat.sub_add_cancel (show 208 ≤ i.val by omega)] using he
                                                      ·
                                                        by_cases h27 : i.val < 224
                                                        · have he := diagonal00Chunk27 ⟨i.val - 216, by omega⟩
                                                          simpa only [Nat.sub_add_cancel (show 216 ≤ i.val by omega)] using he
                                                        ·
                                                          by_cases h28 : i.val < 232
                                                          · have he := diagonal00Chunk28 ⟨i.val - 224, by omega⟩
                                                            simpa only [Nat.sub_add_cancel (show 224 ≤ i.val by omega)] using he
                                                          ·
                                                            by_cases h29 : i.val < 240
                                                            · have he := diagonal00Chunk29 ⟨i.val - 232, by omega⟩
                                                              simpa only [Nat.sub_add_cancel (show 232 ≤ i.val by omega)] using he
                                                            ·
                                                              by_cases h30 : i.val < 248
                                                              · have he := diagonal00Chunk30 ⟨i.val - 240, by omega⟩
                                                                simpa only [Nat.sub_add_cancel (show 240 ≤ i.val by omega)] using he
                                                              ·
                                                                by_cases h31 : i.val < 256
                                                                · have he := diagonal00Chunk31 ⟨i.val - 248, by omega⟩
                                                                  simpa only [Nat.sub_add_cancel (show 248 ≤ i.val by omega)] using he
                                                                ·
                                                                  have he := diagonal00Chunk32 ⟨i.val - 256, by omega⟩
                                                                  simpa only [Nat.sub_add_cancel (show 256 ≤ i.val by omega)] using he

theorem diagonalPA00_correct (m : ℕ) : diagonalPA00 m = (-4) ^ m :=
  cachedPower_sound diagonalPowersA00_valid m

theorem diagonalPS00_correct (m : ℕ) : diagonalPS00 m = 4 ^ m :=
  cachedPower_sound diagonalPowersS00_valid m

theorem diagonalPSign00_correct (m : ℕ) : diagonalPSign00 m = (-1) ^ m :=
  cachedPower_sound diagonalPowersSign00_valid m

theorem diagonal00_semantic_identity :
    IntegerCoefficients.scale diagonalBernsteinDenominator00
      (IntegerCoefficients.affine 256 (fun i ↦ diagonalTree.get i) (-4) 1 4) =
    IntegerCoefficients.scale (4 ^ 256)
      (IntegerCoefficients.expansion 256 (fun i ↦ diagonalBernsteinTree00.get i)) := by
  have h := diagonal00Identity
  rw [diagonalAffine00, diagonalExpansion00,
    IntegerCoefficients.fastAffine_sound Data.choose diagonalPA00 (fun _ ↦ 1)
      diagonalPS00 (-4) 1 4 Data.choose_correct diagonalPA00_correct
      (fun m ↦ (one_pow m).symm) diagonalPS00_correct,
    IntegerCoefficients.fastExpansion_sound Data.choose diagonalPSign00
      Data.choose_correct diagonalPSign00_correct] at h
  exact h

theorem diagonal00_positive {x : ℝ} (hx : x ∈ Set.Icc (-1) (-3 / 4)) :
    0 < evaluate Data.Diagonal x := by
  let t : unitInterval := ⟨4 * (x + 1), by constructor <;> linarith [hx.1, hx.2]⟩
  have h := IntegerCoefficients.positive_affine 256
    (fun i ↦ diagonalTree.get i) (fun i ↦ diagonalBernsteinTree00.get i)
    (-4) 1 4 diagonalBernsteinDenominator00 (by decide +kernel)
    (by decide +kernel) diagonalBernstein00_pos diagonal00_semantic_identity t
  have ht : ((((-4 : ℤ) : ℚ) / (4 : ℤ) : ℚ) : ℝ) +
      ((((1 : ℤ) : ℚ) / (4 : ℤ) : ℚ) : ℝ) * (t : ℝ) = x := by
    dsimp [t]
    norm_num
    ring
  rw [ht] at h
  rw [diagonalCachedRoundtrip, evaluate_scale]
  apply mul_pos _ h
  have hd : (0 : ℤ) < diagonalDenominator := by decide +kernel
  have hdq : (0 : ℚ) < diagonalDenominator := by exact_mod_cast hd
  exact Rat.cast_pos.mpr (one_div_pos.mpr hdq)

end ADMM.UnitCircle.LowerCertificate.Leaves
