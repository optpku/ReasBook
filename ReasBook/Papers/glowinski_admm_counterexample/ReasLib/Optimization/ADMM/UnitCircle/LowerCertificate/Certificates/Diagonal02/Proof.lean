/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal02.Checks00
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal02.Checks01
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal02.Checks02
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal02.Checks03
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal02.Checks04

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal02

theorem coefficient_identity : ∀ i : Fin 257, leftCoefficient i = rightCoefficient i := by
  intro i
  by_cases h0 : i.val < 8
  · simpa only [Nat.add_zero] using chunk00 ⟨i.val, h0⟩
  · by_cases h1 : i.val < 16
    · have he := chunk01 ⟨i.val - 8, by omega⟩
      simpa only [Nat.sub_add_cancel (show 8 ≤ i.val by omega)] using he
    · by_cases h2 : i.val < 24
      · have he := chunk02 ⟨i.val - 16, by omega⟩
        simpa only [Nat.sub_add_cancel (show 16 ≤ i.val by omega)] using he
      · by_cases h3 : i.val < 32
        · have he := chunk03 ⟨i.val - 24, by omega⟩
          simpa only [Nat.sub_add_cancel (show 24 ≤ i.val by omega)] using he
        · by_cases h4 : i.val < 40
          · have he := chunk04 ⟨i.val - 32, by omega⟩
            simpa only [Nat.sub_add_cancel (show 32 ≤ i.val by omega)] using he
          · by_cases h5 : i.val < 48
            · have he := chunk05 ⟨i.val - 40, by omega⟩
              simpa only [Nat.sub_add_cancel (show 40 ≤ i.val by omega)] using he
            · by_cases h6 : i.val < 56
              · have he := chunk06 ⟨i.val - 48, by omega⟩
                simpa only [Nat.sub_add_cancel (show 48 ≤ i.val by omega)] using he
              · by_cases h7 : i.val < 64
                · have he := chunk07 ⟨i.val - 56, by omega⟩
                  simpa only [Nat.sub_add_cancel (show 56 ≤ i.val by omega)] using he
                · by_cases h8 : i.val < 72
                  · have he := chunk08 ⟨i.val - 64, by omega⟩
                    simpa only [Nat.sub_add_cancel (show 64 ≤ i.val by omega)] using he
                  · by_cases h9 : i.val < 80
                    · have he := chunk09 ⟨i.val - 72, by omega⟩
                      simpa only [Nat.sub_add_cancel (show 72 ≤ i.val by omega)] using he
                    · by_cases h10 : i.val < 88
                      · have he := chunk10 ⟨i.val - 80, by omega⟩
                        simpa only [Nat.sub_add_cancel (show 80 ≤ i.val by omega)] using he
                      · by_cases h11 : i.val < 96
                        · have he := chunk11 ⟨i.val - 88, by omega⟩
                          simpa only [Nat.sub_add_cancel (show 88 ≤ i.val by omega)] using he
                        · by_cases h12 : i.val < 104
                          · have he := chunk12 ⟨i.val - 96, by omega⟩
                            simpa only [Nat.sub_add_cancel (show 96 ≤ i.val by omega)] using he
                          · by_cases h13 : i.val < 112
                            · have he := chunk13 ⟨i.val - 104, by omega⟩
                              simpa only [Nat.sub_add_cancel (show 104 ≤ i.val by omega)] using he
                            · by_cases h14 : i.val < 120
                              · have he := chunk14 ⟨i.val - 112, by omega⟩
                                simpa only [Nat.sub_add_cancel (show 112 ≤ i.val by omega)] using he
                              · by_cases h15 : i.val < 128
                                · have he := chunk15 ⟨i.val - 120, by omega⟩
                                  simpa only [Nat.sub_add_cancel (show 120 ≤ i.val by omega)] using he
                                · by_cases h16 : i.val < 136
                                  · have he := chunk16 ⟨i.val - 128, by omega⟩
                                    simpa only [Nat.sub_add_cancel (show 128 ≤ i.val by omega)] using he
                                  · by_cases h17 : i.val < 144
                                    · have he := chunk17 ⟨i.val - 136, by omega⟩
                                      simpa only [Nat.sub_add_cancel (show 136 ≤ i.val by omega)] using he
                                    · by_cases h18 : i.val < 152
                                      · have he := chunk18 ⟨i.val - 144, by omega⟩
                                        simpa only [Nat.sub_add_cancel (show 144 ≤ i.val by omega)] using he
                                      · by_cases h19 : i.val < 160
                                        · have he := chunk19 ⟨i.val - 152, by omega⟩
                                          simpa only [Nat.sub_add_cancel (show 152 ≤ i.val by omega)] using he
                                        · by_cases h20 : i.val < 168
                                          · have he := chunk20 ⟨i.val - 160, by omega⟩
                                            simpa only [Nat.sub_add_cancel (show 160 ≤ i.val by omega)] using he
                                          · by_cases h21 : i.val < 176
                                            · have he := chunk21 ⟨i.val - 168, by omega⟩
                                              simpa only [Nat.sub_add_cancel (show 168 ≤ i.val by omega)] using he
                                            · by_cases h22 : i.val < 184
                                              · have he := chunk22 ⟨i.val - 176, by omega⟩
                                                simpa only [Nat.sub_add_cancel (show 176 ≤ i.val by omega)] using he
                                              · by_cases h23 : i.val < 192
                                                · have he := chunk23 ⟨i.val - 184, by omega⟩
                                                  simpa only [Nat.sub_add_cancel (show 184 ≤ i.val by omega)] using he
                                                · by_cases h24 : i.val < 200
                                                  · have he := chunk24 ⟨i.val - 192, by omega⟩
                                                    simpa only [Nat.sub_add_cancel (show 192 ≤ i.val by omega)] using he
                                                  · by_cases h25 : i.val < 208
                                                    · have he := chunk25 ⟨i.val - 200, by omega⟩
                                                      simpa only [Nat.sub_add_cancel (show 200 ≤ i.val by omega)] using he
                                                    · by_cases h26 : i.val < 216
                                                      · have he := chunk26 ⟨i.val - 208, by omega⟩
                                                        simpa only [Nat.sub_add_cancel (show 208 ≤ i.val by omega)] using he
                                                      · by_cases h27 : i.val < 224
                                                        · have he := chunk27 ⟨i.val - 216, by omega⟩
                                                          simpa only [Nat.sub_add_cancel (show 216 ≤ i.val by omega)] using he
                                                        · by_cases h28 : i.val < 232
                                                          · have he := chunk28 ⟨i.val - 224, by omega⟩
                                                            simpa only [Nat.sub_add_cancel (show 224 ≤ i.val by omega)] using he
                                                          · by_cases h29 : i.val < 240
                                                            · have he := chunk29 ⟨i.val - 232, by omega⟩
                                                              simpa only [Nat.sub_add_cancel (show 232 ≤ i.val by omega)] using he
                                                            · by_cases h30 : i.val < 248
                                                              · have he := chunk30 ⟨i.val - 240, by omega⟩
                                                                simpa only [Nat.sub_add_cancel (show 240 ≤ i.val by omega)] using he
                                                              · by_cases h31 : i.val < 256
                                                                · have he := chunk31 ⟨i.val - 248, by omega⟩
                                                                  simpa only [Nat.sub_add_cancel (show 248 ≤ i.val by omega)] using he
                                                                ·
                                                                  have he := chunk32 ⟨i.val - 256, by omega⟩
                                                                  simpa only [Nat.sub_add_cancel (show 256 ≤ i.val by omega)] using he

theorem semantic_identity :
    IntegerCoefficients.scale bernsteinDenominator
      (IntegerCoefficients.affine 256 (fun k ↦ Leaves.diagonalTree.get k) (-1) 1 2) =
    IntegerCoefficients.scale ((2 : ℤ) ^ 256)
      (IntegerCoefficients.directExpansion Data.choose Data.signPower
        256 (fun k ↦ bernsteinTree.get k)) := by
  apply IntegerCoefficients.identity_of_direct_coefficients Data.choose Data.signPower
    powerA (fun _ ↦ 1) powerS Data.choose_correct (-1) 1 2 bernsteinDenominator
    powerA_correct (fun m ↦ (one_pow m).symm) powerS_correct
  intro i
  have h := coefficient_identity i
  simpa only [leftCoefficient, rightCoefficient, scaleFactor_correct] using h

theorem positive_unit (t : unitInterval) :
    0 < evaluate (List.ofFn (fun k : Fin 257 ↦ (Leaves.diagonalTree.get k : ℚ)))
      ((((-1 : ℤ) : ℚ) / (2 : ℤ) : ℚ) +
        ((((1 : ℤ) : ℚ) / (2 : ℤ) : ℚ) : ℝ) * (t : ℝ)) := by
  exact IntegerCoefficients.positive_affine_direct Data.choose Data.signPower
    Data.choose_correct Data.signPower_correct 256 (fun k ↦ Leaves.diagonalTree.get k)
    (fun k ↦ bernsteinTree.get k) (-1) 1 2 bernsteinDenominator
    (by decide +kernel) bernsteinDenominator_pos coefficients_pos semantic_identity t

theorem positive {x : ℝ} (hx : x ∈ Set.Icc ((-1 / 2) : ℝ) ((0 / 1) : ℝ)) :
    0 < evaluate Data.Diagonal x := by
  let t : unitInterval := ⟨(2 : ℝ) * x - (-1), by
    constructor <;> norm_num at * <;> linarith [hx.1, hx.2]⟩
  have h := positive_unit t
  have ht : ((((-1 : ℤ) : ℚ) / (2 : ℤ) : ℚ) : ℝ) +
      ((((1 : ℤ) : ℚ) / (2 : ℤ) : ℚ) : ℝ) * (t : ℝ) = x := by
    dsimp [t]
    norm_num
    ring
  rw [ht] at h
  rw [Leaves.diagonalCachedRoundtrip, evaluate_scale]
  apply mul_pos _ h
  have hd : (0 : ℤ) < Leaves.diagonalDenominator := by decide +kernel
  have hdq : (0 : ℚ) < Leaves.diagonalDenominator := by exact_mod_cast hd
  exact Rat.cast_pos.mpr (one_div_pos.mpr hdq)

end ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal02
