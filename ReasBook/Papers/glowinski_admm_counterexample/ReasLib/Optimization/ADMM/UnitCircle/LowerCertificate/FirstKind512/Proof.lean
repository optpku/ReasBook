/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check00
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check01
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check02
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check03
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check04
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check05
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check06
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check07
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check08
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check09
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check10
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check11
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check12
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check13
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check14
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Checks.Check15

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.FirstKind512

theorem cache_valid : ChebyshevCacheValid tree.get 512 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tree_get_initial (by decide)]
    exact Data.chebyshevCache_valid.1
  · rw [tree_get_initial (by decide)]
    exact Data.chebyshevCache_valid.2.1
  · intro i
    by_cases hInitial : i.val < 255
    · rw [tree_get_initial (by omega), tree_get_initial (by omega),
        tree_get_initial (by omega)]
      exact Data.chebyshevCache_valid.2.2 ⟨i.val, hInitial⟩
    · by_cases h0 : i.val < 271
      · have he := recurrence00 ⟨i.val - 255, by omega⟩
        simpa only [Nat.sub_add_cancel (show 255 ≤ i.val by omega)] using he
      · by_cases h1 : i.val < 287
        · have he := recurrence01 ⟨i.val - 271, by omega⟩
          simpa only [Nat.sub_add_cancel (show 271 ≤ i.val by omega)] using he
        · by_cases h2 : i.val < 303
          · have he := recurrence02 ⟨i.val - 287, by omega⟩
            simpa only [Nat.sub_add_cancel (show 287 ≤ i.val by omega)] using he
          · by_cases h3 : i.val < 319
            · have he := recurrence03 ⟨i.val - 303, by omega⟩
              simpa only [Nat.sub_add_cancel (show 303 ≤ i.val by omega)] using he
            · by_cases h4 : i.val < 335
              · have he := recurrence04 ⟨i.val - 319, by omega⟩
                simpa only [Nat.sub_add_cancel (show 319 ≤ i.val by omega)] using he
              · by_cases h5 : i.val < 351
                · have he := recurrence05 ⟨i.val - 335, by omega⟩
                  simpa only [Nat.sub_add_cancel (show 335 ≤ i.val by omega)] using he
                · by_cases h6 : i.val < 367
                  · have he := recurrence06 ⟨i.val - 351, by omega⟩
                    simpa only [Nat.sub_add_cancel (show 351 ≤ i.val by omega)] using he
                  · by_cases h7 : i.val < 383
                    · have he := recurrence07 ⟨i.val - 367, by omega⟩
                      simpa only [Nat.sub_add_cancel (show 367 ≤ i.val by omega)] using he
                    · by_cases h8 : i.val < 399
                      · have he := recurrence08 ⟨i.val - 383, by omega⟩
                        simpa only [Nat.sub_add_cancel (show 383 ≤ i.val by omega)] using he
                      · by_cases h9 : i.val < 415
                        · have he := recurrence09 ⟨i.val - 399, by omega⟩
                          simpa only [Nat.sub_add_cancel (show 399 ≤ i.val by omega)] using he
                        · by_cases h10 : i.val < 431
                          · have he := recurrence10 ⟨i.val - 415, by omega⟩
                            simpa only [Nat.sub_add_cancel (show 415 ≤ i.val by omega)] using he
                          · by_cases h11 : i.val < 447
                            · have he := recurrence11 ⟨i.val - 431, by omega⟩
                              simpa only [Nat.sub_add_cancel (show 431 ≤ i.val by omega)] using he
                            · by_cases h12 : i.val < 463
                              · have he := recurrence12 ⟨i.val - 447, by omega⟩
                                simpa only [Nat.sub_add_cancel (show 447 ≤ i.val by omega)] using he
                              · by_cases h13 : i.val < 479
                                · have he := recurrence13 ⟨i.val - 463, by omega⟩
                                  simpa only [Nat.sub_add_cancel (show 463 ≤ i.val by omega)] using he
                                · by_cases h14 : i.val < 495
                                  · have he := recurrence14 ⟨i.val - 479, by omega⟩
                                    simpa only [Nat.sub_add_cancel (show 479 ≤ i.val by omega)] using he
                                  ·
                                    have he := recurrence15 ⟨i.val - 495, by omega⟩
                                    simpa only [Nat.sub_add_cancel (show 495 ≤ i.val by omega)] using he

theorem tree_eval {m : ℕ} (hm : m ≤ 512) (x : ℝ) :
    evaluate (IntegerCoefficients.toRational (tree.get m)) x =
      (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x :=
  chebyshevCache_sound cache_valid hm x

end ADMM.UnitCircle.LowerCertificate.FirstKind512
