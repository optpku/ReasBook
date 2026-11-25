/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower00
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower01
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower02
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower03
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower04
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower05
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower06
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower07
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower08
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower09
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower10
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower11
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower12
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower13
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower14
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower15
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower16
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower17
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower18
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower19
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower20
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower21
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower22
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower23
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower24
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower25
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower26
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower27
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower28
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower29
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower30
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower31
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower32
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower33
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower34
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower35
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower36
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower37
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower38
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower39
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower40
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower41
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower42
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower43
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower44
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower45
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower46
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower47
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower48
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower49
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower50
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower51
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower52
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower53
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower54
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower55
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower56
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower57
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower58
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower59
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower60
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower61
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower62
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower63
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.Lower64

@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

theorem lower_coefficients : ∀ i : Fin 513,
    lowerLeftCoefficient i = lowerRightCoefficient i := by
  intro i
  by_cases h0 : i.val < 8
  · simpa only [Nat.add_zero] using lowerChunk00 ⟨i.val, h0⟩
  ·
    by_cases h1 : i.val < 16
    · have he := lowerChunk01 ⟨i.val - 8, by omega⟩
      simpa only [Nat.sub_add_cancel (show 8 ≤ i.val by omega)] using he
    ·
      by_cases h2 : i.val < 24
      · have he := lowerChunk02 ⟨i.val - 16, by omega⟩
        simpa only [Nat.sub_add_cancel (show 16 ≤ i.val by omega)] using he
      ·
        by_cases h3 : i.val < 32
        · have he := lowerChunk03 ⟨i.val - 24, by omega⟩
          simpa only [Nat.sub_add_cancel (show 24 ≤ i.val by omega)] using he
        ·
          by_cases h4 : i.val < 40
          · have he := lowerChunk04 ⟨i.val - 32, by omega⟩
            simpa only [Nat.sub_add_cancel (show 32 ≤ i.val by omega)] using he
          ·
            by_cases h5 : i.val < 48
            · have he := lowerChunk05 ⟨i.val - 40, by omega⟩
              simpa only [Nat.sub_add_cancel (show 40 ≤ i.val by omega)] using he
            ·
              by_cases h6 : i.val < 56
              · have he := lowerChunk06 ⟨i.val - 48, by omega⟩
                simpa only [Nat.sub_add_cancel (show 48 ≤ i.val by omega)] using he
              ·
                by_cases h7 : i.val < 64
                · have he := lowerChunk07 ⟨i.val - 56, by omega⟩
                  simpa only [Nat.sub_add_cancel (show 56 ≤ i.val by omega)] using he
                ·
                  by_cases h8 : i.val < 72
                  · have he := lowerChunk08 ⟨i.val - 64, by omega⟩
                    simpa only [Nat.sub_add_cancel (show 64 ≤ i.val by omega)] using he
                  ·
                    by_cases h9 : i.val < 80
                    · have he := lowerChunk09 ⟨i.val - 72, by omega⟩
                      simpa only [Nat.sub_add_cancel (show 72 ≤ i.val by omega)] using he
                    ·
                      by_cases h10 : i.val < 88
                      · have he := lowerChunk10 ⟨i.val - 80, by omega⟩
                        simpa only [Nat.sub_add_cancel (show 80 ≤ i.val by omega)] using he
                      ·
                        by_cases h11 : i.val < 96
                        · have he := lowerChunk11 ⟨i.val - 88, by omega⟩
                          simpa only [Nat.sub_add_cancel (show 88 ≤ i.val by omega)] using he
                        ·
                          by_cases h12 : i.val < 104
                          · have he := lowerChunk12 ⟨i.val - 96, by omega⟩
                            simpa only [Nat.sub_add_cancel (show 96 ≤ i.val by omega)] using he
                          ·
                            by_cases h13 : i.val < 112
                            · have he := lowerChunk13 ⟨i.val - 104, by omega⟩
                              simpa only [Nat.sub_add_cancel (show 104 ≤ i.val by omega)] using he
                            ·
                              by_cases h14 : i.val < 120
                              · have he := lowerChunk14 ⟨i.val - 112, by omega⟩
                                simpa only [Nat.sub_add_cancel (show 112 ≤ i.val by omega)] using he
                              ·
                                by_cases h15 : i.val < 128
                                · have he := lowerChunk15 ⟨i.val - 120, by omega⟩
                                  simpa only [Nat.sub_add_cancel (show 120 ≤ i.val by omega)] using he
                                ·
                                  by_cases h16 : i.val < 136
                                  · have he := lowerChunk16 ⟨i.val - 128, by omega⟩
                                    simpa only [Nat.sub_add_cancel (show 128 ≤ i.val by omega)] using he
                                  ·
                                    by_cases h17 : i.val < 144
                                    · have he := lowerChunk17 ⟨i.val - 136, by omega⟩
                                      simpa only [Nat.sub_add_cancel (show 136 ≤ i.val by omega)] using he
                                    ·
                                      by_cases h18 : i.val < 152
                                      · have he := lowerChunk18 ⟨i.val - 144, by omega⟩
                                        simpa only [Nat.sub_add_cancel (show 144 ≤ i.val by omega)] using he
                                      ·
                                        by_cases h19 : i.val < 160
                                        · have he := lowerChunk19 ⟨i.val - 152, by omega⟩
                                          simpa only [Nat.sub_add_cancel (show 152 ≤ i.val by omega)] using he
                                        ·
                                          by_cases h20 : i.val < 168
                                          · have he := lowerChunk20 ⟨i.val - 160, by omega⟩
                                            simpa only [Nat.sub_add_cancel (show 160 ≤ i.val by omega)] using he
                                          ·
                                            by_cases h21 : i.val < 176
                                            · have he := lowerChunk21 ⟨i.val - 168, by omega⟩
                                              simpa only [Nat.sub_add_cancel (show 168 ≤ i.val by omega)] using he
                                            ·
                                              by_cases h22 : i.val < 184
                                              · have he := lowerChunk22 ⟨i.val - 176, by omega⟩
                                                simpa only [Nat.sub_add_cancel (show 176 ≤ i.val by omega)] using he
                                              ·
                                                by_cases h23 : i.val < 192
                                                · have he := lowerChunk23 ⟨i.val - 184, by omega⟩
                                                  simpa only [Nat.sub_add_cancel (show 184 ≤ i.val by omega)] using he
                                                ·
                                                  by_cases h24 : i.val < 200
                                                  · have he := lowerChunk24 ⟨i.val - 192, by omega⟩
                                                    simpa only [Nat.sub_add_cancel (show 192 ≤ i.val by omega)] using he
                                                  ·
                                                    by_cases h25 : i.val < 208
                                                    · have he := lowerChunk25 ⟨i.val - 200, by omega⟩
                                                      simpa only [Nat.sub_add_cancel (show 200 ≤ i.val by omega)] using he
                                                    ·
                                                      by_cases h26 : i.val < 216
                                                      · have he := lowerChunk26 ⟨i.val - 208, by omega⟩
                                                        simpa only [Nat.sub_add_cancel (show 208 ≤ i.val by omega)] using he
                                                      ·
                                                        by_cases h27 : i.val < 224
                                                        · have he := lowerChunk27 ⟨i.val - 216, by omega⟩
                                                          simpa only [Nat.sub_add_cancel (show 216 ≤ i.val by omega)] using he
                                                        ·
                                                          by_cases h28 : i.val < 232
                                                          · have he := lowerChunk28 ⟨i.val - 224, by omega⟩
                                                            simpa only [Nat.sub_add_cancel (show 224 ≤ i.val by omega)] using he
                                                          ·
                                                            by_cases h29 : i.val < 240
                                                            · have he := lowerChunk29 ⟨i.val - 232, by omega⟩
                                                              simpa only [Nat.sub_add_cancel (show 232 ≤ i.val by omega)] using he
                                                            ·
                                                              by_cases h30 : i.val < 248
                                                              · have he := lowerChunk30 ⟨i.val - 240, by omega⟩
                                                                simpa only [Nat.sub_add_cancel (show 240 ≤ i.val by omega)] using he
                                                              ·
                                                                by_cases h31 : i.val < 256
                                                                · have he := lowerChunk31 ⟨i.val - 248, by omega⟩
                                                                  simpa only [Nat.sub_add_cancel (show 248 ≤ i.val by omega)] using he
                                                                ·
                                                                  by_cases h32 : i.val < 264
                                                                  · have he := lowerChunk32 ⟨i.val - 256, by omega⟩
                                                                    simpa only [Nat.sub_add_cancel (show 256 ≤ i.val by omega)] using he
                                                                  ·
                                                                    by_cases h33 : i.val < 272
                                                                    · have he := lowerChunk33 ⟨i.val - 264, by omega⟩
                                                                      simpa only [Nat.sub_add_cancel (show 264 ≤ i.val by omega)] using he
                                                                    ·
                                                                      by_cases h34 : i.val < 280
                                                                      · have he := lowerChunk34 ⟨i.val - 272, by omega⟩
                                                                        simpa only [Nat.sub_add_cancel (show 272 ≤ i.val by omega)] using he
                                                                      ·
                                                                        by_cases h35 : i.val < 288
                                                                        · have he := lowerChunk35 ⟨i.val - 280, by omega⟩
                                                                          simpa only [Nat.sub_add_cancel (show 280 ≤ i.val by omega)] using he
                                                                        ·
                                                                          by_cases h36 : i.val < 296
                                                                          · have he := lowerChunk36 ⟨i.val - 288, by omega⟩
                                                                            simpa only [Nat.sub_add_cancel (show 288 ≤ i.val by omega)] using he
                                                                          ·
                                                                            by_cases h37 : i.val < 304
                                                                            · have he := lowerChunk37 ⟨i.val - 296, by omega⟩
                                                                              simpa only [Nat.sub_add_cancel (show 296 ≤ i.val by omega)] using he
                                                                            ·
                                                                              by_cases h38 : i.val < 312
                                                                              · have he := lowerChunk38 ⟨i.val - 304, by omega⟩
                                                                                simpa only [Nat.sub_add_cancel (show 304 ≤ i.val by omega)] using he
                                                                              ·
                                                                                by_cases h39 : i.val < 320
                                                                                · have he := lowerChunk39 ⟨i.val - 312, by omega⟩
                                                                                  simpa only [Nat.sub_add_cancel (show 312 ≤ i.val by omega)] using he
                                                                                ·
                                                                                  by_cases h40 : i.val < 328
                                                                                  · have he := lowerChunk40 ⟨i.val - 320, by omega⟩
                                                                                    simpa only [Nat.sub_add_cancel (show 320 ≤ i.val by omega)] using he
                                                                                  ·
                                                                                    by_cases h41 : i.val < 336
                                                                                    · have he := lowerChunk41 ⟨i.val - 328, by omega⟩
                                                                                      simpa only [Nat.sub_add_cancel (show 328 ≤ i.val by omega)] using he
                                                                                    ·
                                                                                      by_cases h42 : i.val < 344
                                                                                      · have he := lowerChunk42 ⟨i.val - 336, by omega⟩
                                                                                        simpa only [Nat.sub_add_cancel (show 336 ≤ i.val by omega)] using he
                                                                                      ·
                                                                                        by_cases h43 : i.val < 352
                                                                                        · have he := lowerChunk43 ⟨i.val - 344, by omega⟩
                                                                                          simpa only [Nat.sub_add_cancel (show 344 ≤ i.val by omega)] using he
                                                                                        ·
                                                                                          by_cases h44 : i.val < 360
                                                                                          · have he := lowerChunk44 ⟨i.val - 352, by omega⟩
                                                                                            simpa only [Nat.sub_add_cancel (show 352 ≤ i.val by omega)] using he
                                                                                          ·
                                                                                            by_cases h45 : i.val < 368
                                                                                            · have he := lowerChunk45 ⟨i.val - 360, by omega⟩
                                                                                              simpa only [Nat.sub_add_cancel (show 360 ≤ i.val by omega)] using he
                                                                                            ·
                                                                                              by_cases h46 : i.val < 376
                                                                                              · have he := lowerChunk46 ⟨i.val - 368, by omega⟩
                                                                                                simpa only [Nat.sub_add_cancel (show 368 ≤ i.val by omega)] using he
                                                                                              ·
                                                                                                by_cases h47 : i.val < 384
                                                                                                · have he := lowerChunk47 ⟨i.val - 376, by omega⟩
                                                                                                  simpa only [Nat.sub_add_cancel (show 376 ≤ i.val by omega)] using he
                                                                                                ·
                                                                                                  by_cases h48 : i.val < 392
                                                                                                  · have he := lowerChunk48 ⟨i.val - 384, by omega⟩
                                                                                                    simpa only [Nat.sub_add_cancel (show 384 ≤ i.val by omega)] using he
                                                                                                  ·
                                                                                                    by_cases h49 : i.val < 400
                                                                                                    · have he := lowerChunk49 ⟨i.val - 392, by omega⟩
                                                                                                      simpa only [Nat.sub_add_cancel (show 392 ≤ i.val by omega)] using he
                                                                                                    ·
                                                                                                      by_cases h50 : i.val < 408
                                                                                                      · have he := lowerChunk50 ⟨i.val - 400, by omega⟩
                                                                                                        simpa only [Nat.sub_add_cancel (show 400 ≤ i.val by omega)] using he
                                                                                                      ·
                                                                                                        by_cases h51 : i.val < 416
                                                                                                        · have he := lowerChunk51 ⟨i.val - 408, by omega⟩
                                                                                                          simpa only [Nat.sub_add_cancel (show 408 ≤ i.val by omega)] using he
                                                                                                        ·
                                                                                                          by_cases h52 : i.val < 424
                                                                                                          · have he := lowerChunk52 ⟨i.val - 416, by omega⟩
                                                                                                            simpa only [Nat.sub_add_cancel (show 416 ≤ i.val by omega)] using he
                                                                                                          ·
                                                                                                            by_cases h53 : i.val < 432
                                                                                                            · have he := lowerChunk53 ⟨i.val - 424, by omega⟩
                                                                                                              simpa only [Nat.sub_add_cancel (show 424 ≤ i.val by omega)] using he
                                                                                                            ·
                                                                                                              by_cases h54 : i.val < 440
                                                                                                              · have he := lowerChunk54 ⟨i.val - 432, by omega⟩
                                                                                                                simpa only [Nat.sub_add_cancel (show 432 ≤ i.val by omega)] using he
                                                                                                              ·
                                                                                                                by_cases h55 : i.val < 448
                                                                                                                · have he := lowerChunk55 ⟨i.val - 440, by omega⟩
                                                                                                                  simpa only [Nat.sub_add_cancel (show 440 ≤ i.val by omega)] using he
                                                                                                                ·
                                                                                                                  by_cases h56 : i.val < 456
                                                                                                                  · have he := lowerChunk56 ⟨i.val - 448, by omega⟩
                                                                                                                    simpa only [Nat.sub_add_cancel (show 448 ≤ i.val by omega)] using he
                                                                                                                  ·
                                                                                                                    by_cases h57 : i.val < 464
                                                                                                                    · have he := lowerChunk57 ⟨i.val - 456, by omega⟩
                                                                                                                      simpa only [Nat.sub_add_cancel (show 456 ≤ i.val by omega)] using he
                                                                                                                    ·
                                                                                                                      by_cases h58 : i.val < 472
                                                                                                                      · have he := lowerChunk58 ⟨i.val - 464, by omega⟩
                                                                                                                        simpa only [Nat.sub_add_cancel (show 464 ≤ i.val by omega)] using he
                                                                                                                      ·
                                                                                                                        by_cases h59 : i.val < 480
                                                                                                                        · have he := lowerChunk59 ⟨i.val - 472, by omega⟩
                                                                                                                          simpa only [Nat.sub_add_cancel (show 472 ≤ i.val by omega)] using he
                                                                                                                        ·
                                                                                                                          by_cases h60 : i.val < 488
                                                                                                                          · have he := lowerChunk60 ⟨i.val - 480, by omega⟩
                                                                                                                            simpa only [Nat.sub_add_cancel (show 480 ≤ i.val by omega)] using he
                                                                                                                          ·
                                                                                                                            by_cases h61 : i.val < 496
                                                                                                                            · have he := lowerChunk61 ⟨i.val - 488, by omega⟩
                                                                                                                              simpa only [Nat.sub_add_cancel (show 488 ≤ i.val by omega)] using he
                                                                                                                            ·
                                                                                                                              by_cases h62 : i.val < 504
                                                                                                                              · have he := lowerChunk62 ⟨i.val - 496, by omega⟩
                                                                                                                                simpa only [Nat.sub_add_cancel (show 496 ≤ i.val by omega)] using he
                                                                                                                              ·
                                                                                                                                by_cases h63 : i.val < 512
                                                                                                                                · have he := lowerChunk63 ⟨i.val - 504, by omega⟩
                                                                                                                                  simpa only [Nat.sub_add_cancel (show 504 ≤ i.val by omega)] using he
                                                                                                                                ·
                                                                                                                                  have he := lowerChunk64 ⟨i.val - 512, by omega⟩
                                                                                                                                  simpa only [Nat.sub_add_cancel (show 512 ≤ i.val by omega)] using he

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
