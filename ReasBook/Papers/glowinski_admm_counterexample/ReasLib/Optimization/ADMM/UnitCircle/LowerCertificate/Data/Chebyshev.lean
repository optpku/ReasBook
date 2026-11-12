/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check00
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check01
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check02
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check03
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check04
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check05
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check06
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check07
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check08
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check09
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check10
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check11
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check12
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check13
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check14
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevChecks.Check15

@[expose] public section

set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.Data

theorem chebyshevCache_valid : ChebyshevCacheValid chebyshevTree.get 256 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro i
  by_cases h0 : i.val < 16
  · exact chebyshevRecurrence00 ⟨i.val, h0⟩
  · by_cases h1 : i.val < 32
    · have he := chebyshevRecurrence01 ⟨i.val - 16, by omega⟩
      simpa only [Nat.sub_add_cancel (show 16 ≤ i.val by omega)] using he
    · by_cases h2 : i.val < 48
      · have he := chebyshevRecurrence02 ⟨i.val - 32, by omega⟩
        simpa only [Nat.sub_add_cancel (show 32 ≤ i.val by omega)] using he
      · by_cases h3 : i.val < 64
        · have he := chebyshevRecurrence03 ⟨i.val - 48, by omega⟩
          simpa only [Nat.sub_add_cancel (show 48 ≤ i.val by omega)] using he
        · by_cases h4 : i.val < 80
          · have he := chebyshevRecurrence04 ⟨i.val - 64, by omega⟩
            simpa only [Nat.sub_add_cancel (show 64 ≤ i.val by omega)] using he
          · by_cases h5 : i.val < 96
            · have he := chebyshevRecurrence05 ⟨i.val - 80, by omega⟩
              simpa only [Nat.sub_add_cancel (show 80 ≤ i.val by omega)] using he
            · by_cases h6 : i.val < 112
              · have he := chebyshevRecurrence06 ⟨i.val - 96, by omega⟩
                simpa only [Nat.sub_add_cancel (show 96 ≤ i.val by omega)] using he
              · by_cases h7 : i.val < 128
                · have he := chebyshevRecurrence07 ⟨i.val - 112, by omega⟩
                  simpa only [Nat.sub_add_cancel (show 112 ≤ i.val by omega)] using he
                · by_cases h8 : i.val < 144
                  · have he := chebyshevRecurrence08 ⟨i.val - 128, by omega⟩
                    simpa only [Nat.sub_add_cancel (show 128 ≤ i.val by omega)] using he
                  · by_cases h9 : i.val < 160
                    · have he := chebyshevRecurrence09 ⟨i.val - 144, by omega⟩
                      simpa only [Nat.sub_add_cancel (show 144 ≤ i.val by omega)] using he
                    · by_cases h10 : i.val < 176
                      · have he := chebyshevRecurrence10 ⟨i.val - 160, by omega⟩
                        simpa only [Nat.sub_add_cancel (show 160 ≤ i.val by omega)] using he
                      · by_cases h11 : i.val < 192
                        · have he := chebyshevRecurrence11 ⟨i.val - 176, by omega⟩
                          simpa only [Nat.sub_add_cancel (show 176 ≤ i.val by omega)] using he
                        · by_cases h12 : i.val < 208
                          · have he := chebyshevRecurrence12 ⟨i.val - 192, by omega⟩
                            simpa only [Nat.sub_add_cancel (show 192 ≤ i.val by omega)] using he
                          · by_cases h13 : i.val < 224
                            · have he := chebyshevRecurrence13 ⟨i.val - 208, by omega⟩
                              simpa only [Nat.sub_add_cancel (show 208 ≤ i.val by omega)] using he
                            · by_cases h14 : i.val < 240
                              · have he := chebyshevRecurrence14 ⟨i.val - 224, by omega⟩
                                simpa only [Nat.sub_add_cancel (show 224 ≤ i.val by omega)] using he
                              ·
                                have he := chebyshevRecurrence15 ⟨i.val - 240, by omega⟩
                                simpa only [Nat.sub_add_cancel (show 240 ≤ i.val by omega)] using he

theorem chebyshevTree_eval {m : ℕ} (hm : m ≤ 256) (x : ℝ) :
    evaluate (IntegerCoefficients.toRational (chebyshevTree.get m)) x =
      (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x :=
  chebyshevCache_sound chebyshevCache_valid hm x

end ADMM.UnitCircle.LowerCertificate.Data
