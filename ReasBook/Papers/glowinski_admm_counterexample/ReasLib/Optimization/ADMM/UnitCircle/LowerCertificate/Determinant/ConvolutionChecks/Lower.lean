/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.CoefficientExtensionality
public import Mathlib.Tactic.IntervalCases
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower000
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower001
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower002
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower003
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower004
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower005
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower006
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower007
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower008
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower009
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower010
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower011
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower012
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower013
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower014
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower015
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower016
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower017
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower018
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower019
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower020
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower021
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower022
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower023
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower024
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower025
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower026
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower027
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower028
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower029
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower030
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower031
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower032
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower033
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower034
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower035
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower036
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower037
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower038
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower039
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower040
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower041
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower042
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower043
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower044
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower045
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower046
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower047
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower048
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower049
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower050
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower051
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower052
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower053
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower054
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower055
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower056
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower057
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower058
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower059
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower060
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower061
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower062
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower063
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower064
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower065
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower066
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower067
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower068
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower069
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower070
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower071
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower072
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower073
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower074
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower075
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower076
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower077
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower078
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower079
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower080
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower081
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower082
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower083
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower084
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower085
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower086
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower087
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower088
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower089
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower090
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower091
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower092
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower093
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower094
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower095
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower096
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower097
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower098
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower099
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower100
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower101
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower102
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower103
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower104
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower105
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower106
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower107
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower108
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower109
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower110
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower111
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower112
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower113
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower114
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower115
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower116
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower117
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower118
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower119
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower120
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower121
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower122
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower123
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower124
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower125
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower126
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower127
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectChecks.Lower128

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Determinant

set_option maxHeartbeats 1000000 in
-- Assemble a fixed complete partition of the 1025 checked integer coefficients.
theorem lower_coefficient_checks (i : Fin 1025) :
    lowerDeterminantNumerators.getD i.val 0 =
      directDeterminantCoefficient diagonalCoefficient lowerSecondCoefficient lowerCrossCoefficient i.val := by
  have hbound : i.val / 8 ≤ 128 := by omega
  interval_cases hq : i.val / 8
  · have h := eq_of_beq (lowerCheck000 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 0 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck001 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 8 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck002 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 16 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck003 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 24 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck004 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 32 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck005 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 40 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck006 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 48 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck007 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 56 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck008 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 64 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck009 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 72 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck010 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 80 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck011 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 88 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck012 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 96 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck013 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 104 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck014 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 112 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck015 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 120 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck016 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 128 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck017 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 136 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck018 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 144 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck019 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 152 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck020 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 160 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck021 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 168 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck022 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 176 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck023 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 184 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck024 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 192 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck025 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 200 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck026 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 208 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck027 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 216 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck028 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 224 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck029 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 232 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck030 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 240 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck031 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 248 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck032 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 256 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck033 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 264 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck034 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 272 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck035 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 280 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck036 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 288 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck037 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 296 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck038 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 304 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck039 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 312 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck040 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 320 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck041 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 328 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck042 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 336 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck043 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 344 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck044 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 352 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck045 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 360 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck046 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 368 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck047 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 376 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck048 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 384 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck049 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 392 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck050 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 400 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck051 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 408 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck052 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 416 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck053 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 424 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck054 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 432 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck055 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 440 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck056 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 448 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck057 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 456 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck058 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 464 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck059 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 472 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck060 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 480 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck061 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 488 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck062 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 496 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck063 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 504 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck064 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 512 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck065 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 520 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck066 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 528 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck067 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 536 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck068 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 544 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck069 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 552 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck070 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 560 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck071 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 568 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck072 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 576 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck073 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 584 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck074 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 592 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck075 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 600 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck076 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 608 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck077 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 616 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck078 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 624 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck079 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 632 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck080 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 640 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck081 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 648 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck082 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 656 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck083 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 664 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck084 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 672 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck085 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 680 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck086 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 688 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck087 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 696 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck088 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 704 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck089 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 712 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck090 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 720 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck091 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 728 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck092 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 736 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck093 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 744 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck094 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 752 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck095 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 760 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck096 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 768 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck097 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 776 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck098 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 784 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck099 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 792 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck100 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 800 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck101 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 808 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck102 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 816 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck103 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 824 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck104 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 832 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck105 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 840 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck106 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 848 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck107 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 856 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck108 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 864 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck109 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 872 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck110 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 880 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck111 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 888 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck112 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 896 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck113 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 904 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck114 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 912 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck115 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 920 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck116 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 928 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck117 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 936 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck118 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 944 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck119 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 952 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck120 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 960 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck121 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 968 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck122 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 976 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck123 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 984 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck124 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 992 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck125 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 1000 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck126 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 1008 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck127 ⟨i.val % 8, by exact Nat.mod_lt _ (by decide)⟩)
    have he : 1016 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h
  · have h := eq_of_beq (lowerCheck128 ⟨i.val % 8, by omega⟩)
    have he : 1024 + i.val % 8 = i.val := by omega
    simpa only [Fin.val_mk, he] using h

theorem lower_convolution : lowerDeterminantNumerators =
    determinantVector diagonalNumerators lowerSecondNumerators lowerCrossNumerators := by
  exact determinantVector_eq_of_coefficients lowerDeterminant_length diagonal_length
    lowerSecond_length lowerCross_length diagonalCoefficient_eq lowerSecondCoefficient_eq
    lowerCrossCoefficient_eq lower_coefficient_checks

end ADMM.UnitCircle.LowerCertificate.Determinant
