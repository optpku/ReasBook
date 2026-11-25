/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.CoefficientExtensionality
public import Mathlib.Tactic.IntervalCases
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start000
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start001
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start002
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start003
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start004
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start005
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start006
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start007
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start008
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start009
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start010
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start011
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start012
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start013
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start014
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start015
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start016
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start017
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start018
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start019
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start020
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start021
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start022
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start023
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start024
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start025
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start026
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start027
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start028
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start029
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start030
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start031
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start032
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start033
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start034
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start035
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start036
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start037
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start038
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start039
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start040
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start041
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start042
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start043
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start044
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start045
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start046
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start047
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start048
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start049
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start050
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start051
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start052
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start053
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start054
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start055
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start056
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start057
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start058
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start059
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start060
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start061
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start062
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start063
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start064
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start065
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start066
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start067
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start068
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start069
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start070
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start071
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start072
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start073
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start074
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start075
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start076
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start077
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start078
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start079
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start080
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start081
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start082
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start083
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start084
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start085
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start086
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start087
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start088
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start089
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start090
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start091
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start092
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start093
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start094
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start095
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start096
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start097
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start098
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start099
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start100
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start101
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start102
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start103
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start104
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start105
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start106
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start107
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start108
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start109
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start110
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start111
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start112
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start113
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start114
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start115
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start116
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start117
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start118
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start119
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start120
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start121
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start122
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start123
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start124
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start125
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start126
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start127
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Start128

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Determinant

set_option maxHeartbeats 1000000 in
-- Assemble a fixed complete partition of the 1025 checked integer coefficients.
theorem start_coefficient_checks (i : Fin 1025) :
    startDeterminantNumerators.getD i.val 0 =
      directDeterminantCoefficient diagonalCoefficient startSecondCoefficient startCrossCoefficient i.val := by
  have hbound : i.val / 8 ≤ 128 := by omega
  interval_cases hq : i.val / 8
  · have h := eq_of_beq (startCheck000 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 0 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck001 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 8 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck002 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 16 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck003 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 24 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck004 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 32 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck005 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 40 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck006 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 48 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck007 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 56 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck008 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 64 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck009 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 72 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck010 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 80 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck011 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 88 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck012 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 96 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck013 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 104 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck014 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 112 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck015 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 120 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck016 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 128 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck017 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 136 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck018 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 144 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck019 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 152 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck020 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 160 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck021 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 168 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck022 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 176 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck023 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 184 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck024 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 192 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck025 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 200 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck026 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 208 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck027 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 216 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck028 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 224 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck029 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 232 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck030 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 240 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck031 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 248 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck032 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 256 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck033 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 264 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck034 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 272 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck035 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 280 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck036 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 288 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck037 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 296 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck038 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 304 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck039 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 312 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck040 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 320 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck041 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 328 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck042 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 336 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck043 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 344 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck044 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 352 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck045 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 360 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck046 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 368 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck047 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 376 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck048 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 384 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck049 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 392 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck050 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 400 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck051 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 408 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck052 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 416 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck053 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 424 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck054 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 432 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck055 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 440 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck056 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 448 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck057 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 456 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck058 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 464 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck059 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 472 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck060 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 480 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck061 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 488 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck062 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 496 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck063 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 504 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck064 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 512 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck065 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 520 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck066 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 528 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck067 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 536 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck068 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 544 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck069 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 552 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck070 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 560 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck071 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 568 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck072 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 576 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck073 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 584 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck074 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 592 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck075 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 600 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck076 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 608 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck077 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 616 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck078 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 624 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck079 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 632 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck080 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 640 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck081 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 648 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck082 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 656 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck083 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 664 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck084 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 672 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck085 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 680 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck086 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 688 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck087 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 696 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck088 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 704 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck089 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 712 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck090 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 720 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck091 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 728 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck092 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 736 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck093 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 744 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck094 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 752 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck095 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 760 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck096 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 768 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck097 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 776 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck098 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 784 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck099 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 792 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck100 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 800 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck101 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 808 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck102 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 816 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck103 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 824 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck104 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 832 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck105 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 840 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck106 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 848 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck107 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 856 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck108 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 864 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck109 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 872 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck110 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 880 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck111 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 888 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck112 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 896 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck113 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 904 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck114 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 912 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck115 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 920 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck116 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 928 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck117 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 936 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck118 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 944 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck119 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 952 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck120 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 960 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck121 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 968 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck122 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 976 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck123 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 984 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck124 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 992 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck125 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 1000 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck126 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 1008 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck127 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 1016 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (startCheck128 ⟨i.val % 8, by omega⟩)
    have he : 1024 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h

theorem start_convolution : startDeterminantNumerators =
    determinantVector diagonalNumerators startSecondNumerators startCrossNumerators := by
  exact determinantVector_eq_of_coefficients startDeterminant_length diagonal_length
    startSecond_length startCross_length diagonalCoefficient_eq startSecondCoefficient_eq
    startCrossCoefficient_eq start_coefficient_checks

end ADMM.UnitCircle.LowerCertificate.Determinant
