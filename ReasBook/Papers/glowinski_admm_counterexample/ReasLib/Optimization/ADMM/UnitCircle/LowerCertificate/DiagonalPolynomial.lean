/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FiniteChecks
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DiagonalChebyshevSemantics
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check00
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check01
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check02
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check03
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check04
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check05
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check06
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check07
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check08
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check09
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check10
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check11
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check12
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check13
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check14
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check15
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check16
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check17
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check18
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check19
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check20
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check21
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check22
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check23
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check24
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check25
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check26
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check27
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check28
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check29
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check30
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check31
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevChecks.Check32

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate

theorem diagonalChebPolynomial_identity : Data.diagonalChebPolynomial =
    List.ofFn (fun i : Fin 257 ↦ Leaves.diagonalTree.get i) := by
  apply list_eq_of_getD _ _ 0 257 Data.diagonalChebPolynomial_length (by simp only [List.length_ofFn])
  intro i
  have hq : (List.ofFn (fun j : Fin 257 ↦ Leaves.diagonalTree.get j)).getD i 0 =
      Leaves.diagonalTree.get i := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]
  rw [hq]
  by_cases h0 : i.val < 8
  · simpa only [Nat.add_zero] using Data.diagonalChebChunk00 ⟨i.val, h0⟩
  · by_cases h1 : i.val < 16
    · have he := Data.diagonalChebChunk01 ⟨i.val - 8, by omega⟩
      simpa only [Nat.sub_add_cancel (show 8 ≤ i.val by omega)] using he
    · by_cases h2 : i.val < 24
      · have he := Data.diagonalChebChunk02 ⟨i.val - 16, by omega⟩
        simpa only [Nat.sub_add_cancel (show 16 ≤ i.val by omega)] using he
      · by_cases h3 : i.val < 32
        · have he := Data.diagonalChebChunk03 ⟨i.val - 24, by omega⟩
          simpa only [Nat.sub_add_cancel (show 24 ≤ i.val by omega)] using he
        · by_cases h4 : i.val < 40
          · have he := Data.diagonalChebChunk04 ⟨i.val - 32, by omega⟩
            simpa only [Nat.sub_add_cancel (show 32 ≤ i.val by omega)] using he
          · by_cases h5 : i.val < 48
            · have he := Data.diagonalChebChunk05 ⟨i.val - 40, by omega⟩
              simpa only [Nat.sub_add_cancel (show 40 ≤ i.val by omega)] using he
            · by_cases h6 : i.val < 56
              · have he := Data.diagonalChebChunk06 ⟨i.val - 48, by omega⟩
                simpa only [Nat.sub_add_cancel (show 48 ≤ i.val by omega)] using he
              · by_cases h7 : i.val < 64
                · have he := Data.diagonalChebChunk07 ⟨i.val - 56, by omega⟩
                  simpa only [Nat.sub_add_cancel (show 56 ≤ i.val by omega)] using he
                · by_cases h8 : i.val < 72
                  · have he := Data.diagonalChebChunk08 ⟨i.val - 64, by omega⟩
                    simpa only [Nat.sub_add_cancel (show 64 ≤ i.val by omega)] using he
                  · by_cases h9 : i.val < 80
                    · have he := Data.diagonalChebChunk09 ⟨i.val - 72, by omega⟩
                      simpa only [Nat.sub_add_cancel (show 72 ≤ i.val by omega)] using he
                    · by_cases h10 : i.val < 88
                      · have he := Data.diagonalChebChunk10 ⟨i.val - 80, by omega⟩
                        simpa only [Nat.sub_add_cancel (show 80 ≤ i.val by omega)] using he
                      · by_cases h11 : i.val < 96
                        · have he := Data.diagonalChebChunk11 ⟨i.val - 88, by omega⟩
                          simpa only [Nat.sub_add_cancel (show 88 ≤ i.val by omega)] using he
                        · by_cases h12 : i.val < 104
                          · have he := Data.diagonalChebChunk12 ⟨i.val - 96, by omega⟩
                            simpa only [Nat.sub_add_cancel (show 96 ≤ i.val by omega)] using he
                          · by_cases h13 : i.val < 112
                            · have he := Data.diagonalChebChunk13 ⟨i.val - 104, by omega⟩
                              simpa only [Nat.sub_add_cancel (show 104 ≤ i.val by omega)] using he
                            · by_cases h14 : i.val < 120
                              · have he := Data.diagonalChebChunk14 ⟨i.val - 112, by omega⟩
                                simpa only [Nat.sub_add_cancel (show 112 ≤ i.val by omega)] using he
                              · by_cases h15 : i.val < 128
                                · have he := Data.diagonalChebChunk15 ⟨i.val - 120, by omega⟩
                                  simpa only [Nat.sub_add_cancel (show 120 ≤ i.val by omega)] using he
                                · by_cases h16 : i.val < 136
                                  · have he := Data.diagonalChebChunk16 ⟨i.val - 128, by omega⟩
                                    simpa only [Nat.sub_add_cancel (show 128 ≤ i.val by omega)] using he
                                  · by_cases h17 : i.val < 144
                                    · have he := Data.diagonalChebChunk17 ⟨i.val - 136, by omega⟩
                                      simpa only [Nat.sub_add_cancel (show 136 ≤ i.val by omega)] using he
                                    · by_cases h18 : i.val < 152
                                      · have he := Data.diagonalChebChunk18 ⟨i.val - 144, by omega⟩
                                        simpa only [Nat.sub_add_cancel (show 144 ≤ i.val by omega)] using he
                                      · by_cases h19 : i.val < 160
                                        · have he := Data.diagonalChebChunk19 ⟨i.val - 152, by omega⟩
                                          simpa only [Nat.sub_add_cancel (show 152 ≤ i.val by omega)] using he
                                        · by_cases h20 : i.val < 168
                                          · have he := Data.diagonalChebChunk20 ⟨i.val - 160, by omega⟩
                                            simpa only [Nat.sub_add_cancel (show 160 ≤ i.val by omega)] using he
                                          · by_cases h21 : i.val < 176
                                            · have he := Data.diagonalChebChunk21 ⟨i.val - 168, by omega⟩
                                              simpa only [Nat.sub_add_cancel (show 168 ≤ i.val by omega)] using he
                                            · by_cases h22 : i.val < 184
                                              · have he := Data.diagonalChebChunk22 ⟨i.val - 176, by omega⟩
                                                simpa only [Nat.sub_add_cancel (show 176 ≤ i.val by omega)] using he
                                              · by_cases h23 : i.val < 192
                                                · have he := Data.diagonalChebChunk23 ⟨i.val - 184, by omega⟩
                                                  simpa only [Nat.sub_add_cancel (show 184 ≤ i.val by omega)] using he
                                                · by_cases h24 : i.val < 200
                                                  · have he := Data.diagonalChebChunk24 ⟨i.val - 192, by omega⟩
                                                    simpa only [Nat.sub_add_cancel (show 192 ≤ i.val by omega)] using he
                                                  · by_cases h25 : i.val < 208
                                                    · have he := Data.diagonalChebChunk25 ⟨i.val - 200, by omega⟩
                                                      simpa only [Nat.sub_add_cancel (show 200 ≤ i.val by omega)] using he
                                                    · by_cases h26 : i.val < 216
                                                      · have he := Data.diagonalChebChunk26 ⟨i.val - 208, by omega⟩
                                                        simpa only [Nat.sub_add_cancel (show 208 ≤ i.val by omega)] using he
                                                      · by_cases h27 : i.val < 224
                                                        · have he := Data.diagonalChebChunk27 ⟨i.val - 216, by omega⟩
                                                          simpa only [Nat.sub_add_cancel (show 216 ≤ i.val by omega)] using he
                                                        · by_cases h28 : i.val < 232
                                                          · have he := Data.diagonalChebChunk28 ⟨i.val - 224, by omega⟩
                                                            simpa only [Nat.sub_add_cancel (show 224 ≤ i.val by omega)] using he
                                                          · by_cases h29 : i.val < 240
                                                            · have he := Data.diagonalChebChunk29 ⟨i.val - 232, by omega⟩
                                                              simpa only [Nat.sub_add_cancel (show 232 ≤ i.val by omega)] using he
                                                            · by_cases h30 : i.val < 248
                                                              · have he := Data.diagonalChebChunk30 ⟨i.val - 240, by omega⟩
                                                                simpa only [Nat.sub_add_cancel (show 240 ≤ i.val by omega)] using he
                                                              · by_cases h31 : i.val < 256
                                                                · have he := Data.diagonalChebChunk31 ⟨i.val - 248, by omega⟩
                                                                  simpa only [Nat.sub_add_cancel (show 248 ≤ i.val by omega)] using he
                                                                ·
                                                                  have he := Data.diagonalChebChunk32 ⟨i.val - 256, by omega⟩
                                                                  simpa only [Nat.sub_add_cancel (show 256 ≤ i.val by omega)] using he

theorem diagonalPolynomial_source (x : ℝ) :
    evaluate Data.Diagonal x = (realPolynomial Division.startDiagonalQuotient).eval x -
      (ADMM.RefinedEndpoint.Data.kappa : ℝ) := by
  calc
    evaluate Data.Diagonal x =
        evaluate (IntegerCoefficients.toRational Data.diagonalChebPolynomial) x /
          Leaves.diagonalDenominator := by
      rw [Leaves.diagonalCachedRoundtrip, evaluate_scale, diagonalChebPolynomial_identity]
      simp only [IntegerCoefficients.toRational, List.map_ofFn, Function.comp_def,
        Rat.cast_div, Rat.cast_one, Rat.cast_intCast]
      ring
    _ = _ := (diagonalCheb_source_eval x).symm

theorem startDiagonal_margin_firstLeaf {z : ℂ} (hz : ‖z‖ = 1)
    (hx : z.re ∈ Set.Icc (-1) (-3 / 4)) :
    (ADMM.RefinedEndpoint.Data.kappa : ℝ) <
      (evaluateLaurent Division.startDiagonalQuotient z).re := by
  rw [evaluateLaurent_re _ hz]
  have h := Leaves.diagonal00_positive hx
  rw [diagonalPolynomial_source] at h
  linarith

end ADMM.UnitCircle.LowerCertificate
